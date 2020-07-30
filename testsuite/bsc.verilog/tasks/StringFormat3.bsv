(* synthesize *)
module sysStringFormat3();
   
   Reg#(Bit#(64)) count <- mkReg(0);

   rule is_3 (count == 3);
      Bit#(80) x <- $swriteAV("zow X%3hX X%3hX X%3hX", count[7:0], count[9:0], count);
      $display("K%sK", x);
   endrule
   
   rule every;
      count <= count + 1;
      if (count == 10) $finish(0);
   endrule

endmodule
