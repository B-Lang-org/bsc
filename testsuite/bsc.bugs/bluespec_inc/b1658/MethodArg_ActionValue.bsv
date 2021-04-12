typedef Bit#(80) WideT;

interface ProcessIfc;
   method ActionValue#(WideT) processVal(WideT val);
endinterface

(* synthesize *)
module mkMethodArg_ActionValue_Sub (ProcessIfc);
   method ActionValue#(WideT) processVal(WideT val);
      return val;
   endmethod
endmodule

(* synthesize *)
module sysMethodArg_ActionValue ();
   ProcessIfc p <- mkMethodArg_ActionValue_Sub;

   Reg#(Bool) done <- mkReg(False);

   rule rl_disp (!done);
      WideT old_val = '1;
      WideT new_val <- p.processVal(old_val);
      $display("old: %h", old_val);
      $display("new: %h", new_val);
      done <= True;
   endrule

   rule rl_done (done);
      $finish(0);
   endrule

endmodule

