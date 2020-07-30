import RegFile::*;
import FIFO::*;
import StmtFSM::*;
import Cache::*;
import External_Interfaces::*;
import SRAM_Interfaces::*;

typedef union tagged {
    Addr Init;
    void Init_Done;
    void Running_Tests;
} Testbench_State deriving(Bits);

(*synthesize*)
module testbench();
    IFC_Cache dut <- cache();
   
    Reg#(Testbench_State) tb_state <- mkReg(Init(0));

    // expected reply to the next cache read
    FIFO#(SRAM_Response_t#(Line)) expected_cache_resp <- mkFIFO();

    // hold expected requests by cache to memory, for comparison with responses
    FIFO#(SRAM_Request_t#(Addr, Line)) expected_mem_req <- mkFIFO();
   
    // delayed main memory response when the cache controller asks
    FIFO#(SRAM_Response_t#(Line)) mem_resp <- mkFIFO();
   
    // used to initialize memory at reset
    Reg #(Addr) count_init <- mkReg(0);
    
    // cycle counter
    Reg#(int) counter <- mkReg(0);
    
    // count failed tests
    Reg#(int) test_failures <- mkReg(0);
   
    // fake "main memory" for the cache to talk to
    RegFile #(Addr, Line) main_mem <- mkRegFile(0,31);

    function Action cache_read(Addr addr, Line expected_val, Bool expect_mem_req);
        action
            dut.proc.p2c(SRAM_Read { address: addr });
            if (expect_mem_req)
                expected_mem_req.enq(SRAM_Read { address: addr });
            expected_cache_resp.enq(SRAM_Response_t { data: expected_val });
            $display("INFO (testbench): issuing read %h", addr);
        endaction
    endfunction
   
    function Action cache_write(Addr addr, Line val);
        action
            dut.proc.p2c(SRAM_Write { address: addr, data: val });
            $display("INFO (testbench): issuing write %h <- %h", addr, val);
        endaction
    endfunction    
    
    Stmt test_seq =
         seq action cache_read({19'h0,8'h0,5'h0}, 0, True); endaction 
             action cache_read({19'h1,8'h0,5'h0}, 2, True); endaction
             action cache_read({19'h0,8'h0,5'h0}, 0, False); endaction
             action cache_read({19'h1,8'h0,5'h0}, 2, False); endaction
             action cache_read({19'h2,8'h0,5'h0}, 4, True); endaction
             action cache_write({19'h3,8'h0,5'h0}, 'hcc00cc); endaction
             action cache_write({19'h2,8'h0,5'h0}, 'hdd00dd); endaction
             action cache_read({19'h2,8'h0,5'h0}, 'hdd00dd, False); endaction
             // three writes and reads -- if cache writes to both lines,
             // one of these should fail
             action cache_write({19'h1,8'h0,5'h0}, 'hb0a8bead); endaction
             action cache_read({19'h1,8'h0,5'h0}, 'hb0a8bead, False); endaction                 
             action cache_write({19'h1,8'h0,5'h0}, 'hdeadbeef); endaction
             action cache_read({19'h1,8'h0,5'h0}, 'hdeadbeef, False); endaction                 
             action cache_write({19'h1,8'h0,5'h0}, 'hbadf00d); endaction
             action cache_read({19'h1,8'h0,5'h0}, 'hbadf00d, False); endaction                 
         endseq;

    // make an FSM from the test sequence
    FSM test_fsm <- mkFSM(test_seq);
    
    rule process_cache_result;
         $display ("INFO (testbench) cache read result = %h ", dut.proc.c2p.data);
         expected_cache_resp.deq();
         if (dut.proc.c2p != expected_cache_resp.first())
             begin
                 test_failures <= test_failures + 1;
                 $display("FAIL: cache read result %h (expected %h)",
                          dut.proc.c2p, expected_cache_resp.first());
             end
    endrule

    // the assumption is that the memory will have a read delay
    // otherwise, what's the point of caching it?  ;)
    rule process_mem_read_request(dut.mem.c2m matches tagged SRAM_Read { address: .a });
        $display("INFO (testbench) main memory load from %h:", a);
        $display("INFO (testbench)   %h", main_mem.sub({a[12:0],a[31:13]}));
        if (!(expected_mem_req.first() == dut.mem.c2m))
            begin
                test_failures <= test_failures + 1;
                $display("FAIL: cache memory request does not match expected");
                $display("      expected: %h", expected_mem_req.first());
                $display("      received: %h", dut.mem.c2m);
            end
        mem_resp.enq(SRAM_Response_t { data: main_mem.sub({a[12:0],a[31:13]}) });
        expected_mem_req.deq();
    endrule
    
    rule send_mem_read_response;
        dut.mem.m2c(mem_resp.first());
        mem_resp.deq();
    endrule

    rule process_mem_write(dut.mem.c2m matches
                           tagged SRAM_Write { address: .a, data: .d });
         $display ("INFO (testbench) main memory store at %h:", a);
         $display ("INFO (testbench)   %h", d);
         main_mem.upd ({a[12:0],a[31:13]}, d);
    endrule 

    rule init_memory(tb_state matches tagged Init .count);
        main_mem.upd(count,  {0,count << 1});
        case (count)
            31: tb_state <= Init_Done;
            default: tb_state <= Init(count + 1);
        endcase
        case (count)
            0: $display("INFO (testbench) initializing testbench memory...");
            31: $display("INFO (testbench) testbench memory initialized");
        endcase
    endrule
    
    rule run_tests(tb_state matches Init_Done);
        test_fsm.start();
        tb_state <= Running_Tests;
    endrule

    rule finish(tb_state matches tagged Running_Tests
                &&& test_fsm.done());
        if (test_failures == 0)
            $display("STATUS: all tests passed");
        else
            $display("STATUS: %d tests failed", test_failures);
        $finish(0);
    endrule
endmodule

