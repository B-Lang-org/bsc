
// Test for the pretting printing of the show schedule dump

(* synthesize *)
module sysPPrintSched ();

   
   Reg#(Int#(8)) i1 <- mkReg(0);
   Reg#(Int#(8)) i2 <- mkReg(2);
   Reg#(Int#(8)) i3 <- mkReg(2);
   Reg#(Bit#(11))  b11 <- mkReg(0);
   Reg#(Bit#(3))  b3 <- mkReg(0);

   PulseWire xpw <- mkPulseWire ; // no short hand for pw._read

   function Bool testcase();
      return (case (b3)
              3'h0 : return (i1 == i2);
              3'h1 : return (i1 != i2) ? i2 == i3 : False ;
              3'h2 : return (i1 == i2);
              3'h3 : return (i3 == i2);
              default : return i1 < 7 ? (i2==i1) : (i1+i2==i3);
             endcase);
   endfunction
   
   rule noSim ;
      $finish(0);
   endrule
   
   rule r1 (i1 < (i2 + 1));
      $display("r1");
   endrule
   
   rule r1a (i1 + i2 + i3 == 0);
      $display("r1a");
   endrule
   
   rule r1b ((i1 + i2) + i3 == 0);
      $display("r1b");
   endrule
   
   rule r1c (i1 + (i2 + i3) == 0);
      $display("r1c");
   endrule
         
   rule r1d (i1 + (i2 - i3) == 0);
      $display("r1d");
   endrule

   
   rule r2 (b11[4:0] == 0 );
      $display("r2");
   endrule
   
   rule r3 (test1(i2, i3) != test1(i2, i1));
      $display("r3");
   endrule
   
   rule r4 ( {b11[4], b11[3], b11[10], b11[7:6]} == 5'h1c);
      $display("r4");
   endrule
   
   rule r5( pack(i2-i1)[3:0] == 4'h8);
      $display("r5");
      xpw.send ;
   endrule

   rule r6( testcase );
      $display("r6");
   endrule
   
   rule r6a( xpw && testcase );
      $display("r6a");
   endrule

   rule r7( (unpack(b11[0])) || ((b11[10:9] == 2'b11) && testcase) );
      $display("r7");
   endrule
      
   
endmodule


(* noinline *)
function Bool test1(Int#(8) x, Int#(8) y);
   return (x+1) == y ;
endfunction
