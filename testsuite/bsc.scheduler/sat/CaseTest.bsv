
// Test dynamic case selection where the case arms are exclusive
// case(idx) { x0 x1 x2 x3 } == ! case(idx) { !x0 !x1 !x2 !x3 }

(*synthesize*)
module sysCaseTest();
   Reg#(Bool) u0 <- mkReg(False);
   Reg#(Bool) u1 <- mkReg(False);
   Reg#(Bool) u2 <- mkReg(False);
   Reg#(Bool) u3 <- mkReg(False);

   // register to make the selection dynamic
   Reg#(Bit#(2)) idx <- mkReg(0);

   Bool pa;
   case (idx)
      0 : pa = u0;
      1 : pa = u1;
      2 : pa = u2;
      default : pa = u3;
   endcase
   
   Bool pb;
   case (idx)
      0 : pb = !u0;
      1 : pb = !u1;
      2 : pb = !u2;
      default : pb = !u3;
   endcase

   // register to make the rule Actions conflict
   Reg#(UInt#(12)) uc <- mkReg(0);

   // predicates for aa and ab are disjoint

   rule aa (pa);
      uc <= uc + 1;
   endrule

   rule ab (pb);
      uc <= uc + 2;
   endrule

   //  expect warning that bb can never fire
   rule  bb (idx == 0);
      uc <= uc + 3;
   endrule

endmodule
