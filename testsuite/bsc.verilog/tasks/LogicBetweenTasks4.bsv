
// Make the timestamps (and thus the output) match in Bluesim and Verilog
// by accouting for the negedge execution of tasks in Verilog
//
function ActionValue#(Bit#(32)) my_time ();
   actionvalue
      let r <- $stime();
/*
      // correct for Verilog's negedge
      if (genVerilog)
         return (r + 5);
      else
*/
         return (r);
   endactionvalue
endfunction

// -------------------------

interface Ifc;
  method Action   m1 (Bit#(32) x);
  method Bit#(32) m2 ();
endinterface

(* synthesize *)
module mkLogicBetweenTasks4_Sub (Ifc);
   Wire#(Bit#(32)) w1 <- mkWire;
   Wire#(Bit#(32)) w2 <- mkWire;
   Reg#(Bit#(32)) rg <- mkReg('1);

   rule r1;
     let v3 = ~ w1;
     $display("sub v3 = %b", v3);
   endrule

   rule r2;
      let v1 <- my_time;
      $display("sub v1 = %b", v1);

      //let v2 = v1 + 1;
      //$display("sub v2 = %b", v2);

      //w2 <= v2;
      w2 <= v1;
   endrule

   method Action m1(x);
     w1 <= x;
   endmethod

   method m2() = w2;

endmodule

// -------------------------

(* synthesize *)
module sysLogicBetweenTasks4 ();
   Reg#(Bit#(32)) state <- mkReg(0);

   Ifc sub <- mkLogicBetweenTasks4_Sub;

   rule r1 (state == 0);
      let v1 <- my_time();
      $display("v1 = %b", v1);

      //let v2 = v1 + 1;
      //$display("v2 = %b", v2);

      //sub.m1(v2);
      sub.m1(v1);
   endrule

   rule r2 (state == 0);
      let v3 = ~ sub.m2;
      $display("v3 = %b", v3);
      state <= state + 1;
   endrule

   rule r3 (state == 1);
      $finish(0);
   endrule

endmodule
