(* synthesize *)
module sysValuePlusargs ();
   Reg#(Bool) b <- mkReg(True);
   Reg#(Bit#(128)) result <- mkReg(12345678);
   rule disp_rule (b);
      let v <- $value$plusargs("e=%d",result);
      if(v)
         $display("$value$plusargs = %h", result);
      else
         $display("$value$plusargs is not given");
      b <= False;
      $finish(0);
   endrule
endmodule
