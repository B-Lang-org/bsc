// -------------------------

interface Ifc;
  method Bit#(32) m(Bit#(32) x);
endinterface

(* synthesize *)
module mkLogicBetweenTasks3_Sub (Ifc);
   Reg#(Bit#(32)) rg <- mkReg('1);
   method m(x) = ~x & rg;
endmodule

// -------------------------

(* synthesize *)
module sysLogicBetweenTasks3 ();
   Reg#(Bit#(32)) state <- mkReg(0);

   Ifc sub <- mkLogicBetweenTasks3_Sub;

   // Make the timestamps (and thus the output) match in Bluesim and Verilog
   // by accouting for the negedge execution of tasks in Verilog
   //
   function ActionValue#(Bit#(32)) my_time ();
      actionvalue
	 let r <- $stime();
	 // correct for Verilog's negedge
	 if (genVerilog)
	    return (r + 5);
	 else
	    return (r);
      endactionvalue
   endfunction

   rule r1 (state == 0);
      let v1 <- my_time();
      $display("v1 = %b", v1);

      // Test when the logic is in a separately synthesized module
      //
      // But also include some logic in this module, that needs to apply
      // before the outside logic.  The wrapper on $stime will do this
      // for Verilog, but ensure that Bluesim is also testing it by
      // including some here.
      //
      let v2 = v1 + 1;
      $display("v2 = %b", v2);
      let s1 = sub.m(v2);
      $display("s1 = %b", s1);
      $display();

      state <= state + 1;
   endrule

   rule r2 (state == 1);
      $finish(0);
   endrule

endmodule
