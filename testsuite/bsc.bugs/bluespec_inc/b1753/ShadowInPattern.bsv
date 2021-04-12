
(* synthesize *)
module sysShadowInPattern();

   Reg#(Maybe#(UInt#(5))) ending <- mkReg(Invalid);
   Reg#(Maybe#(UInt#(5))) lastdata <- mkReg(Invalid);

   rule process;
      Maybe#(UInt#(5)) en = ending;
      Maybe#(UInt#(5)) mn = lastdata;

      // Patterns are handled fine:
      // the match of "mn" creates a new def of "en" that shadows explicit
      // uses of "en" because it gets added to the environment, but it does
      // not redefine "en" in the expr that gets substituted for "m",
      // because it's not actually creating a let-binding for "en"
      if (en matches tagged Valid .m &&&
          // shadow en
          mn matches tagged Valid .en &&&
	  // use m, which was defined in terms of en
	  (m == 3)) begin
         $display("Hi");
      end
   endrule

endmodule

