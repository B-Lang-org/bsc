typedef Bit#(80) WideT;

interface ProcessIfc;
   method WideT processVal(WideT val);
endinterface

(* synthesize *)
module mkMethodArg_Value_Sub (ProcessIfc);
   method WideT processVal(WideT val);
      return val;
   endmethod
endmodule

(* synthesize *)
module sysMethodArg_Value ();
   ProcessIfc p <- mkMethodArg_Value_Sub;

   Reg#(Bool) done <- mkReg(False);

   rule rl_disp (!done);
      WideT old_val = '1;
      WideT new_val = p.processVal(old_val);
      $display("old: %h", old_val);
      $display("new: %h", new_val);
      done <= True;
   endrule

   rule rl_done (done);
      $finish(0);
   endrule

endmodule

