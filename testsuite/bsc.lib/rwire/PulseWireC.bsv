

(* synthesize *)
module sysPulseWireC ();

   Reg#(Bit#(10)) c <- mkReg(0);
   Reg#(Bit#(10)) x <- mkReg(0);

   rule cnt ;
      c <= c + 1;
      if (c > 50) $finish(0);
   endrule

   PulseWire cpw <- mkPulseWire ;

   (* descending_urgency="r2,r1" *)
   rule r1 ( c[1:0] == 0 );
      cpw.send ;
      $display( "%d:  r1 fires", c);
   endrule

   rule r2 ( c[2:0] == 0 );
      cpw.send ;
      $display( "%d:  r2 fires", c);
   endrule

   rule pwread (cpw);
      $display ("%d:  pulseWire is set", c);
   endrule



endmodule
