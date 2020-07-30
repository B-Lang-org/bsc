//Testbench which is calling deq every cycle
//So in case of Empty Fifo if enq and deq is called every cycle
//It should execute both in same clock cycle(logically enq before deq)
import GetPut::*;
import Top::*;

module mkTestbench(Empty);

Get#(Bit#(5)) top <- mkTop;
Reg#(Bit#(5)) sim_cnt <- mkReg(0);

(* fire_when_enabled *)
rule deq_out(True);
    let dout <- top.get();
    $display($time, "\tData out = %d", dout);
endrule

(* no_implicit_conditions, fire_when_enabled *)
rule ctrl_sim(True);
    sim_cnt <= sim_cnt + 1;
    if(sim_cnt == 14)
        $finish(0);
endrule

endmodule
