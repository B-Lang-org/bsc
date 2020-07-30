(* synthesize *)
module sysArrayLength_ArrSel_2D();

   Reg#(Bit#(3))               idx <- mkReg(0);

   Bit#(5)                     tbl[8][3] = {
      { 0, 0, 0 }, { 0, 0, 1 }, { 0, 1, 0 }, { 0, 1, 1 },
      { 1, 0, 0 }, { 1, 0, 1 }, { 1, 1, 0 }, { 1, 1, 1 }
   };

   rule r;
      // Test that the error branch is not evaluated
      if (arrayLength(tbl[idx]) != 3)
         // further test that the static string operations are pushed
	 // through the dynamic expressions (otherwise we get nfError)
         error("bad length " + integerToString(arrayLength(tbl[idx])));
         //error("bad length");
      else
         $display("3");
   endrule
endmodule

