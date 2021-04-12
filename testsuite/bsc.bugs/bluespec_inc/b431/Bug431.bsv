function Bit#(8) showbug( Bit#(8) a );
   Bit#(8) res;
   res = 0;
   if (a[3:0] != 0)
      res = 11;
   return res;
endfunction

(* synthesize *)
module sysBug431();
   rule displayBug(True);
     $display("res = %0d; showbug(res) = %0d", 0, showbug(0));
     $display("res = %0d; showbug(res) = %0d", 1, showbug(1));
     $finish(0);
   endrule
endmodule
