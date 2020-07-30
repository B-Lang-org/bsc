(* synthesize *)
module sysPolymorphicTaskInPolymorphicFunc();
   rule every;
      Bit#(48) zow <- zwrite;
      $display(zow);
   endrule
endmodule

function ActionValue#(Bit#(n)) zwrite();
   return($swriteAV("XXX"));
endfunction

