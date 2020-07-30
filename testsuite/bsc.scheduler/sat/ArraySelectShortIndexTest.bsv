
// Test dynamic array selection where the array elements are exclusive
// sel(idx, array x0 x1 x2 x3) == ! sel(idx, array !x0 !x1 !x2 !x3)

// This differs from ArraySelectTest in that the index can only select
// a strict subset of the array (2-bit index, 6 elements)

(*synthesize*)
module sysArraySelectShortIndexTest();
   Bool   vals[6];
   Bool   notvals[6];
   for (Integer i = 0; i < 6; i = i + 1) begin
      Reg#(Bool) rg <- mkReg(False);
      vals[i] = rg;
      notvals[i] = !rg;
   end

   // register to make the selection dynamic
   Reg#(Bit#(2)) idx <- mkReg(0);

   // register to make the rule Actions conflict
   Reg#(UInt#(12)) uc <- mkReg(0);

   // predicates for aa and ab are disjoint

   rule aa (vals[idx]);
      uc <= uc + 1;
   endrule

   rule ab (notvals[idx]);
      uc <= uc + 2;
   endrule

   //  expect warning that bb can never fire
   rule  bb (idx == 0);
      uc <= uc + 3;
   endrule

endmodule
