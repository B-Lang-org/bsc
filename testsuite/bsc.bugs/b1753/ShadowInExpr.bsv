
(* synthesize *)
module sysShadowInExpr();

   Reg#(Maybe#(UInt#(5))) ending <- mkReg(Invalid);
   Reg#(Maybe#(UInt#(5))) lastdata <- mkReg(Invalid);

   rule process;
      Maybe#(UInt#(5)) en = ending;
      Maybe#(UInt#(5)) mn = Invalid;

      if (en matches tagged Valid .m) begin
	 en = tagged Valid (m+1);
	 mn = tagged Valid (m+1);
      end

      ending <= en;
      lastdata <= mn;

   endrule

endmodule

