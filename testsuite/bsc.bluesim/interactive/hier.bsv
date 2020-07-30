(* synthesize *)
module mkTop();
   
  Empty mid1 <- mkMid(13);
  Empty mid2 <- mkMid(7);
  Empty level1 <- mkLevel1();
   
  Reg#(UInt#(16)) count <- mkReg(0);

  rule incr (count < 100);
    count <= count + 1;
    $display("%t: %d", $time(), count);
  endrule: incr

  rule done (count == 100);
    $finish(0);
  endrule: done

endmodule

(* synthesize *)
module mkMid(UInt#(4) limit, Empty ifc);
   Empty sub1 <- mkSub();
   Reg#(UInt#(4)) count <- mkReg(0);
   
   rule incr (count < limit);
      count <= count + 1;
   endrule: incr
   
   rule wrap (count == limit);
      $display("wrap in %m");
      count <= 0;
   endrule: wrap
endmodule

module mkSub();
   Reg#(Bool) x <- mkReg(False);
   
   rule flip;
      x <= !x;
      $display("%m: %b", x);
   endrule
endmodule

(* synthesize *)
module mkLevel1();
   Empty level2 <- mkMid(5);
endmodule
