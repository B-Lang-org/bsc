(* synthesize *)
module mkSub2(UInt#(8) limit, Empty ifc);

   Reg#(UInt#(8)) count <- mkReg(0);

   rule incr;
      count <= count + 1;
   endrule: incr
   
   rule done (count == limit);
      $finish(0);
   endrule: done
   
endmodule: mkSub2