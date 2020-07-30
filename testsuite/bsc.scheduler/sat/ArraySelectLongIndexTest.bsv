
// Test dynamic array selection where the array elements are exclusive
// sel(idx, array x0 x1 x2 x3) == ! sel(idx, array !x0 !x1 !x2 !x3)

// This differs from ArraySelectTest in that the index can select
// off the end of the array (3-bit index, 5 elements)

(*synthesize*)
module sysArraySelectLongIndexTest();
   Bool   vals[5];
   Bool   notvals[5];
   for (Integer i = 0; i < 5; i = i + 1) begin
      Reg#(Bool) rg <- mkReg(False);
      vals[i] = rg;
      notvals[i] = !rg;
   end

   // register to make the selection dynamic
   Reg#(Bit#(3)) idx <- mkReg(0);

   // register to make the rule Actions conflict
   Reg#(UInt#(12)) uc <- mkReg(0);

   // predicates for aa and ab are disjoint

   rule aa ((idx < 5) && vals[idx]);
      uc <= uc + 1;
   endrule

   rule ab ((idx < 5) && notvals[idx]);
      uc <= uc + 2;
   endrule

   //  expect warning that bb can never fire
   rule  bb (idx < 5);
      uc <= uc + 3;
   endrule

endmodule
