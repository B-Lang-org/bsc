(* synthesize *)
module mkBlockingTest();
   Reg#(UInt#(8)) count  <- mkReg(0);
   Reg#(UInt#(8)) count2 <- mkReg(0);
   Reg#(UInt#(8)) count3 <- mkReg(0);
   
   rule incr;
      count <= count + 1;
   endrule
   
   (* descending_urgency = "r1,r2,r3,r4" *)
   rule r1 (count > 4);
      count2 <= count2 + 1;
   endrule

   rule r2 (count < 12);
      count2 <= count2 + 2;
   endrule

   rule r3 (count % 3 == 1);
      count2 <= count2 + 3;
   endrule

   rule r4;
      count2 <= count2 + 4;
   endrule

   (* descending_urgency = "ra,rb,rc" *)
   rule ra (count2 % 5 == 2);
      count3 <= count3 + 3;
   endrule

   rule rb (count2 > 3);
      count3 <= count3 + 2;
   endrule

   rule rc;
      count3 <= count3 + 1;
   endrule
   
   rule done (count3 > 100);
      $finish(0);
   endrule
   
endmodule
