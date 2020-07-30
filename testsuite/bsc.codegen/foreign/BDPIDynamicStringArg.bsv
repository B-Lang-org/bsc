import "BDPI" function Bit#(32) my_stoi (String x);

(* synthesize *)
module mkBDPIDynamicStringArg ();
   Reg#(UInt#(2)) count <- mkReg(0);

   rule incr(count < 3);
       count <= count + 1;
   endrule: incr

   rule r;
      let str = (count == 0) ? "0x17" : (count == 1) ? "8736255" : (count == 2) ? "0xbeef" : "42";
      $display("%d",my_stoi(str));
   endrule

   rule done(count == 3);
       $finish(0);
   endrule: done

endmodule
