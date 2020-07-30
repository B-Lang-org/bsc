(* synthesize *)
module sysMethodConds_Function ();
   Reg#(UInt#(8)) s <- mkRegU;

   Reg#(Bool) c1 <- mkRegU;
   Reg#(Bool) c2 <- mkRegU;
   Reg#(Bool) c3 <- mkRegU;

   function Action zeroS();
      action
         s <= 0;
      endaction
   endfunction

   function Action setS(UInt#(8) v);
      action
         s <= v;
      endaction
   endfunction

   rule r;
      if (c1) begin
         if (c2)
            setS(17);
         else if (c3)
            s <= 2;
         else
	    zeroS();
      end
      else begin
         if (c2)
            zeroS();
         else if (c3)
            setS(42);
         else
            s <= 2;
      end
   endrule                    
endmodule

