(* synthesize *)
module sysSelDefaultFail();

   // Test also when the index can't go off the end?
   Reg#(Bit#(3))   idx <- mkReg(0);

   Integer         tbl[4] = { 0, 0, 1, 0 };

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
      // One of the elements doesn't meet this condition, so we expect
      // the error to be triggered.
      //
      if (get(idx) != 0)
         error("bad value");
      else
         $display("OK");
   endrule
endmodule

