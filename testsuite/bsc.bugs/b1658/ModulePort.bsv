typedef Bit#(80) WideT;

interface ProcessIfc;
   method WideT processVal();
endinterface

(* synthesize *)
module mkModulePort_Sub #(WideT val) (ProcessIfc);
   method WideT processVal();
      return val;
   endmethod
endmodule

(* synthesize *)
module sysModulePort ();
   WideT old_val = '1;
   ProcessIfc p <- mkModulePort_Sub(old_val);

   Reg#(Bool) done <- mkReg(False);

   rule rl_disp (!done);
      WideT new_val = p.processVal();
      $display("old: %h", old_val);
      $display("new: %h", new_val);
      done <= True;
   endrule

   rule rl_done (done);
      $finish(0);
   endrule

endmodule

