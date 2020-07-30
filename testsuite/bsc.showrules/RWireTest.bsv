(* synthesize *)
module mkRWireTest();
   Reg#(UInt#(8))   count  <- mkReg(0);
   Reg#(UInt#(8))   count2 <- mkReg(0);
   RWire#(UInt#(4)) rw     <- mkRWire();

   rule incr;
      count <= count + 1;
   endrule
   
   rule send (count % 4  == 3);
      rw.wset(truncate(count >> 2));
   endrule

   rule recv (rw.wget() matches tagged Valid .x);
      count2 <= count2 + extend(x);
   endrule
   
   rule done (count > 100);
      $finish(0);
   endrule
   
endmodule
