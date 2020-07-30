(* synthesize *)
module sysSelDefaultElse();

   // Test also when the index can't go off the end?
   Reg#(Bit#(3))   idx <- mkReg(0);

   Integer         tbl[4] = { 0, 0, 0, 0 };

   function Integer get(Bit#(3) i);
      return tbl[i];
/*
      if (i == 0) return tbl[0];
      else if (i == 1) return tbl[1];
      else if (i == 2) return tbl[2];
      else if (i == 3) return tbl[3];
      else return ?;
*/
   endfunction

   rule r;
      // In this test, the error is the "else" branch; if the selection
      // returns a don't-care value, maybe "if _ t e" will reduce to "e"?
      // SelDefault tests for the error being in the "then" branch.
      //
      if (get(idx) == 0)
         $display("OK");
      else
         // further test that the static string operations are pushed
	 // through the dynamic expressions (otherwise we get nfError)
         error("bad value");
         //error("bad value: " + integerToString(get(idx)));
   endrule
endmodule

