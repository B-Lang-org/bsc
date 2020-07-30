import RegFile::*;
import FIFO::*;
import StmtFSM::*;
import Cache::*;
import External_Interfaces::*;
import SRAM_Interfaces::*;
import LFSR::*;

typedef union tagged {
    Addr Init;
    void Init_Done;
    void Running_Tests;
} Testbench_State deriving(Bits);

(*synthesize*)
module random_testbench();
    IFC_Cache dut <- cache();

    Reg#(Testbench_State) tb_state <- mkReg(Init(0));

    // expected reply to the next cache read
    FIFO#(SRAM_Response_t#(Line)) expected_cache_resp <- mkFIFO();

    // delayed main memory response when the cache controller asks
    FIFO#(SRAM_Response_t#(Line)) mem_resp <- mkFIFO();

    //Randomized cache hit testing
    FIFO#(Addr) test_hit <- mkFIFO();

    // used to initialize memory at reset
    Reg #(Addr) count_init <- mkReg(0);

    // cycle counter
    Reg#(int) counter <- mkReg(0);

    // count failed tests
    Reg#(int) test_failures <- mkReg(0);

    // fake "main memory" for the cache to talk to
    RegFile #(Addr, Line) main_mem <- mkRegFile(0,255);

    LFSR#(Bit#(8)) psrand <- mkFeedLFSR(54);
    LFSR#(Addr) randloc <- mkFeedLFSR(32'hdeadbeef);
    LFSR#(Line) randline <- mkFeedLFSR(256'hdeadbeefdeedbeefdeadbeafdeafbeefdeafeeefbeadbeeffeedbeefeeeebee0);


    function Action cache_read(Addr addr, Line expected_val);
        action
            dut.proc.p2c(SRAM_Read { address: addr });
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

    (* descending_urgency = "test_hits, test_read, test_write" *)
    rule test_hits (psrand.value() > 60);
      Addr rloc = test_hit.first();
      cache_read(rloc, main_mem.sub({24'd0, rloc[7:0]}));
      counter <= counter + 1;
      test_hit.deq();
    endrule

    rule test_read (psrand.value() < 30);
      Addr rloc = {randloc.value()[26:0], 5'd0};
      cache_read(rloc, main_mem.sub({24'd0, rloc[7:0]}));
      counter <= counter + 1;
      if (psrand.value() < 5)
        test_hit.enq(rloc);
    endrule

    rule test_write (psrand.value() >= 30);
      Addr rloc = {randloc.value()[26:0], 5'd0};
      cache_write(rloc, randline.value());
      counter <= counter + 1;
      //A write-through cache means we don't update main memory here.
    endrule

    rule advance_rand (True);
      psrand.next();
      randloc.next();
      randline.next();
    endrule

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
        $display("INFO (testbench)   %h", main_mem.sub({24'd0, a[7:0]}));
        mem_resp.enq(SRAM_Response_t { data: main_mem.sub({24'd0, a[7:0]}) });
    endrule

    rule send_mem_read_response;
        dut.mem.m2c(mem_resp.first());
        mem_resp.deq();
    endrule

    rule process_mem_write(dut.mem.c2m matches
                           tagged SRAM_Write { address: .a, data: .d });
         $display ("INFO (testbench) main memory store at %h:", a);
         $display ("INFO (testbench)   %h", d);
         main_mem.upd ({24'd0, a[7:0]}, d);
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
        tb_state <= Running_Tests;
    endrule

    rule finish(tb_state matches tagged Running_Tests
                &&& counter == 1000);
        if (test_failures == 0)
            $display("STATUS: all tests passed");
        else
            $display("STATUS: %d tests failed", test_failures);
        $finish(0);
    endrule
endmodule
