
(* synthesize *)
module sysBug1753();

   Reg#(Maybe#(UInt#(5))) ending <- mkReg(Invalid);
   Reg#(Maybe#(UInt#(5))) lastdata <- mkReg(Invalid);

   rule process;
      let en = ending;
      Maybe#(UInt#(5)) mn = Invalid;

      if (en matches tagged Valid .m) begin
	 en = Invalid;
	 mn = tagged Valid (m-4);
      end

      ending <= en;
      lastdata <= mn;

   endrule

endmodule

