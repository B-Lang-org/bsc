// Two-way Associative Cache Controller
//
// The controller has three main interfaces:
//   - interface to the processor which makes memory read/write requests
//   - interface to the main memory which this controller is caching
//   - interfaces to three SRAMs which hold the cache data and tags
//     - two cache-line SRAMs: one for each "way"
//     - one "tag" SRAM: valid and tag bits for cache entries
//
// Operation
//   Two request types are supported: reads and writes
//   When a read results in a cache hit, the response must appear
//   in the next cycle (given one-cycle cache/tag SRAMs)
//   When a read results in a cache miss, the response time is best-effort;
//   the cache line for the entry just read is updated; the cache is busy
//   until the memory read comes back and the cache entry is updated.
//   Writes are passed through to the main memory and update the cache entry.
//   At reset, the cache is initialized with all entries invalid;
//   this takes the number of cycles equal to the number of cache lines.
//   The cache is ready for a request every cycle, except during a read miss.
//
// Implementation
//   1. At reset, all cache entries are invalidated (rule initialize);
//      during this, state is Initializing, and, after init, changes to Ready
//   2. If the cache state is Ready and last_cpu_request is empty,
//      the processor may make a request via method p2c.  p2c forwards
//      the request to the cache SRAMs, and writes the processor request
//      to last_cpu_request.
//   3. In the next cycle, the cache SRAM responds
//      a. last request was write (rule process_last_write):
//         forward the write request to the main memory
//         if a cache line already contains the written address, replace it;
//         otherwise replace the next line to be evicted (round-robin)
//         remove the cpu request from last_cpu_request
//      b. last request was read (rule process_last_read):
//         if a valid tag matches the address, the response is put on rwire
//         c2p_data, and must be read by method c2p
//         if no valid tag matches, the request is forwarded to main memory,
//         and the cache enters a busy state (Waiting_For_Memory)
//         the request remains in last_cpu_request until main memory responds
//   4. While the controller waits for the main memory, it continuously requests
//      the cache line at the relevant address (rule request_cache_tag)
//   5. When the main memory responds to the read request (method m2c),
//      the response is written to the cache and to c2p_data rwire

import External_Interfaces::*;
import SRAM_Interfaces::*;
import FIFO::*;

typedef Bit #(18) Tag;
typedef Bit #(9) Indx;

interface IFC_Cache_Controller;
    interface IFC_Cache_Processor proc;
    interface IFC_Cache_Memory mem;
    interface IFC_SRAM_Client#(Indx, Line) cache_way0;
    interface IFC_SRAM_Client#(Indx, Line) cache_way1;
    interface IFC_SRAM_Client#(Indx, Cache_Tag#(Tag)) cache_tag;
endinterface: IFC_Cache_Controller

typedef enum {
    Initializing,       // cache tags being invalidated after reset
    Ready,              // ready to accept next request
    Waiting_For_Memory  // waiting for a read from main memory
} State deriving (Bits, Eq);

// cache tags in cache SRAMs
// data invariant:
//   tag_way0 == Nothing || tag_way0 != tag_way1
// whenever the cache is operational
typedef struct {
    Maybe#(tag_t) tag_way0;
    Maybe#(tag_t) tag_way1;
    Bool next_evict_way0;
} Cache_Tag#(type tag_t) deriving(Bits);

(* synthesize *)
module cache_controller(IFC_Cache_Controller);
    // controller state (see definition of State above)
    Reg#(State) state <- mkReg(Initializing);

    // which cache location we're clearing (used only during post-reset init)
    Reg #(bit[8:0]) cache_init_location <- mkReg(0);

    // response to the processor
    RWire#(Line) c2p_data <- mkRWire();

    // last request the cpu made (e.g., previous cycle)
    FIFO#(SRAM_Request_t#(Addr, Line)) last_cpu_request <- mkFIFO1();

    // requests going to real memory
    RWire #(SRAM_Request_t#(Addr, Line)) c2memory_req <- mkRWire;

    // wires for asynchronous communication with cache SRAMs:
    // - cache tag request and response
    RWire#(SRAM_Request_t#(Indx,Cache_Tag#(Tag))) tag_req <- mkRWire();
    RWire#(SRAM_Response_t#(Cache_Tag#(Tag))) cache_tag_resp <- mkRWire();
    // - way 0 request and response
    RWire#(SRAM_Request_t#(Indx,Line)) way0_req <- mkRWire();
    RWire#(SRAM_Response_t#(Line)) way0_resp <- mkRWire();
    // - way 1 request and response
    RWire#(SRAM_Request_t#(Indx,Line)) way1_req <- mkRWire();
    RWire#(SRAM_Response_t#(Line)) way1_resp <- mkRWire();

    // at reset time, invalidate the contents of the cache
    rule initialize(state == Initializing);
        let invalidate_write_data =
                Cache_Tag { tag_way0: Invalid, tag_way1: Invalid,
                            next_evict_way0: True };
        let invalidate_req =
                SRAM_Write { address: cache_init_location,
                             data: invalidate_write_data };
        tag_req.wset(invalidate_req);
        state <= cache_init_location == 511 ? Ready : Initializing;
        // case (cache_init_location)
            // 0: $display("INFO (cache controller) initializing cache...");
            // 511: $display("INFO (cache controller) cache initialized.");
        // endcase
        cache_init_location <= cache_init_location + 1;
    endrule

    // when a line comes back from the cache, check if it's valid: if it is,
    // send it back to the processor; otherwise, ask the cached memory
    rule process_last_read(state == Ready
                           &&& last_cpu_request.first() matches
                              tagged SRAM_Read { address: .orig_addr }
                           &&& cache_tag_resp.wget() matches tagged Valid .resp_tag
                           &&& way0_resp.wget() matches tagged Valid .resp_way0
                           &&& way1_resp.wget() matches tagged Valid .resp_way1);
        function same_as_orig(tag) = (tag == orig_addr[31:14]);
        let orig_tag = orig_addr[31:14];

        case (resp_tag.data) matches
            tagged Cache_Tag { tag_way0: tagged Valid .tag } &&& same_as_orig(tag):
                begin
                    c2p_data.wset(resp_way0.data);
                    last_cpu_request.deq();
                    // $display("INFO (cache controller) way0 matches tag %h", orig_tag);
                end
            tagged Cache_Tag { tag_way1: tagged Valid .tag } &&& same_as_orig(tag):
                begin
                    c2p_data.wset(resp_way1.data);
                    last_cpu_request.deq();
                    // $display("INFO (cache controller) way1 matches tag %h", orig_tag);
                end
            default: // no hits, talk to cached memory
                begin
                    c2memory_req.wset(last_cpu_request.first());
                    state <= Waiting_For_Memory;
                    // $display("INFO (cache controller) nothing matches tag %h", orig_tag);
                end
        endcase
    endrule: process_last_read

    // if the last request was a write, replace relevant cache entry
    // and propagate write to main memory
    rule process_last_write(state == Ready
                            &&& last_cpu_request.first() matches
                                  tagged SRAM_Write { address: .orig_addr, data: .orig_data }
                            &&& cache_tag_resp.wget() matches tagged Valid .resp_tag);
        let line_req = SRAM_Write { address: orig_addr[13:5], data: orig_data };
        function same_as_orig(tag) = (tag == orig_addr[31:14]);
        Bool evict_way0;
        case (resp_tag.data) matches
            tagged Cache_Tag { tag_way0: tagged Valid .tag } &&& same_as_orig(tag):
                evict_way0 = True;
            tagged Cache_Tag { tag_way1: tagged Valid .tag } &&& same_as_orig(tag):
                evict_way0 = False;
            default: evict_way0 = resp_tag.data.next_evict_way0;
        endcase
        if (evict_way0)
            begin
                let new_tag = Cache_Tag { next_evict_way0: !resp_tag.data.next_evict_way0,
                                          tag_way0: Valid (orig_addr[31:14]),
                                          tag_way1: resp_tag.data.tag_way1 };
                let new_tag_req = SRAM_Write { address: orig_addr[13:5],
                                               data: new_tag };
                way0_req.wset(line_req);
                tag_req.wset(new_tag_req);
                // $display("INFO (cache controller) writing tag %h at %h to way0",
                         // orig_addr[31:14], orig_addr[13:5]);
            end
        else
            begin
                let new_tag = Cache_Tag { next_evict_way0: !resp_tag.data.next_evict_way0,
                                          tag_way0: resp_tag.data.tag_way0,
                                          tag_way1: Valid (orig_addr[31:14]) };
                let new_tag_req = SRAM_Write { address: orig_addr[13:5],
                                               data: new_tag };
                way1_req.wset(line_req);
                tag_req.wset(new_tag_req);
                // $display("INFO (cache controller) writing tag %h at %h to way1",
                         // orig_addr[31:14], orig_addr[13:5]);
            end
        c2memory_req.wset(last_cpu_request.first());
        last_cpu_request.deq(); // remove if there's an ack protocol
        state <= Ready; // Waiting_For_Memory if there's an ack protocol;
    endrule

    // while waiting for the main memory, keep requesting the cache tag
    // so that we know where to write things back
    rule request_cache_tag(state == Waiting_For_Memory
                           &&& last_cpu_request.first() matches
                                   tagged SRAM_Read { address: .addr });
        tag_req.wset(SRAM_Read { address: addr[13:5] });
    endrule

    // interface to the processor
    interface IFC_Cache_Processor proc;
        // when a processor makes a request, forward it to the cache memories
        // immediately, and register the request for later comparison
        method Action p2c (cpu_request) if (state == Ready);
            begin
                case (cpu_request) matches
                    // if it's a read, read the cache, and wait for a response
                    tagged SRAM_Read { address: .addr }:
                        begin
                            let req = SRAM_Read { address: addr[13:5] };
                            tag_req.wset(req);
                            way0_req.wset(req);
                            way1_req.wset(req);
                            // $display("INFO (cache controller) p2c: read %h", addr);
                        end
                    // if it's a write, read the cache to find out what to evict
                    tagged SRAM_Write { address: .addr }:
                        begin
                            let req = SRAM_Read { address: addr[13:5] };
                            tag_req.wset(req);
                            way0_req.wset(req);
                            way1_req.wset(req);
                            // $display("INFO (cache controller) p2c: write %h", addr);
                        end
                endcase
                last_cpu_request.enq(cpu_request);
            end
        endmethod: p2c

        // let the processor read our response whenever the response is ready
        method  c2p if (c2p_data.wget matches tagged Valid .resp);
            return (SRAM_Response_t { data: resp });
        endmethod: c2p
    endinterface: proc

    // interface to the memory we're caching
    interface IFC_Cache_Memory mem;
        method c2m() if (c2memory_req.wget matches tagged Valid .req);
            return req;
        endmethod

        // a memory read request has come back: write the new value
        // to the relevant cache line, and send it to the processor ifc
        method Action m2c(mem_resp)
                if (state == Waiting_For_Memory
                    &&& last_cpu_request.first() matches
                        tagged SRAM_Read { address: .orig_addr });
            // cache response must be valid (rule request_cache_tag ensures this)
            match tagged SRAM_Response_t { data: .resp_tag } =
                validValue (cache_tag_resp.wget());
            match tagged SRAM_Response_t { data: .mem_data } = mem_resp;
            // $display("INFO (cache controller) mem response");
            // $display("INFO (cache controller)   %h", mem_data);
            let line_req = SRAM_Write { address: orig_addr[13:5], data: mem_data };
            if (resp_tag.next_evict_way0)
                begin
                    let new_tag = Cache_Tag { next_evict_way0: !resp_tag.next_evict_way0,
                                              tag_way0: Valid (orig_addr[31:14]),
                                              tag_way1: resp_tag.tag_way1 };
                    let new_tag_req = SRAM_Write { address: orig_addr[13:5],
                                                   data: new_tag };
                    way0_req.wset(line_req);
                    tag_req.wset(new_tag_req);
                    // $display("INFO (cache controller) replacing tag %h at way0", orig_addr[31:14]);
                end
            else
                begin
                    let new_tag = Cache_Tag { next_evict_way0: !resp_tag.next_evict_way0,
                                              tag_way0: resp_tag.tag_way0,
                                              tag_way1: Valid (orig_addr[31:14]) };
                    let new_tag_req = SRAM_Write { address: orig_addr[13:5],
                                                   data: new_tag };
                    way1_req.wset(line_req);
                    tag_req.wset(new_tag_req);
                    // $display("INFO (cache controller) replacing tag %h at way1", orig_addr[31:14]);
                end
            c2p_data.wset(mem_data);
            last_cpu_request.deq();
            state <= Ready;
        endmethod: m2c
    endinterface: mem

    // interface to the cache tag SRAM
    interface IFC_SRAM_Client cache_tag;
        method SRAM_Request_t#(Indx, Cache_Tag#(Tag)) get_request()
                if (tag_req.wget() matches (tagged Valid .req));
            return req;
        endmethod
        method Action set_response(SRAM_Response_t#(Cache_Tag#(Tag)) resp);
            cache_tag_resp.wset(resp);
        endmethod
    endinterface: cache_tag

    // interface to way-0 cache SRAM
    interface IFC_SRAM_Client cache_way0;
        method SRAM_Request_t#(Indx, Line) get_request()
                if (way0_req.wget() matches (tagged Valid .req));
            return req;
        endmethod
        method Action set_response(SRAM_Response_t#(Line) resp);
            way0_resp.wset(resp);
        endmethod
    endinterface: cache_way0

    // interface to way-1 cache SRAM
    interface IFC_SRAM_Client cache_way1;
        method SRAM_Request_t#(Indx, Line) get_request()
                if (way1_req.wget() matches (tagged Valid .req));
            return req;
        endmethod
        method Action set_response(SRAM_Response_t#(Line) resp);
            way1_resp.wset(resp);
        endmethod
    endinterface: cache_way1
endmodule: cache_controller
