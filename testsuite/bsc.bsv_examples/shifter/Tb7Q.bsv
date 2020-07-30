/*----------------------------------------------------------------------------

Testbench for Example7Q

The expected output is:

Testing Ls:
16'hFFFF << 4'b0000 = 16'b1111111111111111
16'hFFFF << 4'b0001 = 16'b1111111111111110
16'hFFFF << 4'b0010 = 16'b1111111111111100
16'hFFFF << 4'b0011 = 16'b1111111111111000
16'hFFFF << 4'b0100 = 16'b1111111111110000
16'hFFFF << 4'b0101 = 16'b1111111111100000
16'hFFFF << 4'b0110 = 16'b1111111111000000
16'hFFFF << 4'b0111 = 16'b1111111110000000
16'hFFFF << 4'b1000 = 16'b1111111100000000
16'hFFFF << 4'b1001 = 16'b1111111000000000
16'hFFFF << 4'b1010 = 16'b1111110000000000
16'hFFFF << 4'b1011 = 16'b1111100000000000
16'hFFFF << 4'b1100 = 16'b1111000000000000
16'hFFFF << 4'b1101 = 16'b1110000000000000
16'hFFFF << 4'b1110 = 16'b1100000000000000
16'hFFFF << 4'b1111 = 16'b1000000000000000
Testing LsV2:
16'hFFFF << 4'b0000 = 16'b1111111111111111
16'hFFFF << 4'b0001 = 16'b1111111111111110
16'hFFFF << 4'b0010 = 16'b1111111111111100
16'hFFFF << 4'b0011 = 16'b1111111111111000
Sending clear:
16'hFFFF << 4'b1000 = 16'b1111111100000000
16'hFFFF << 4'b1001 = 16'b1111111000000000
16'hFFFF << 4'b1010 = 16'b1111110000000000
16'hFFFF << 4'b1011 = 16'b1111100000000000
16'hFFFF << 4'b1100 = 16'b1111000000000000
16'hFFFF << 4'b1101 = 16'b1110000000000000
16'hFFFF << 4'b1110 = 16'b1100000000000000
16'hFFFF << 4'b1111 = 16'b1000000000000000
Done
 
-----------------------------------------------------------------------------*/

import FIFO::*;
import Example7Q::*;

typedef union tagged {
   void    Start;
   Bit#(4) Ls;
   Bit#(4) LsV2;
   void    Clear;
   void    Done;	      
} State deriving (Eq, Bits);

module mkTb7 (Empty);

   // DUTs
   
   FIFO#(SXpair#(4,16)) ls();
   mkLs the_ls(ls);

   FIFO#(SXpair#(4,16)) lsv2();
   mkLsV2 the_lsv2(lsv2);

   // Testbench state
   
   Reg#(State) send_state();
   mkReg#(Start) send_state_r(send_state);

   Reg#(State) recv_state();
   mkReg#(Start) recv_state_r(recv_state);

   // Send rules

   rule send_start (send_state matches tagged Start);
      $display("Testing Ls:");
      send_state <= Ls(0);
      recv_state <= Ls(0);
   endrule

   rule send_Ls (send_state matches tagged Ls .s);
      ls.enq(tuple2(s, 16'hFFFF));
      if (s == 15)
	 send_state <= LsV2(0);
      else
	 send_state <= Ls(s+1);
   endrule

   rule send_LsV2 (send_state matches tagged LsV2 .s);
      lsv2.enq(tuple2(s, 16'hFFFF));
      if (s == 15)
	 send_state <= Done;
      else
      // test clear half way through
      if (s == 7)
	 send_state <= Clear;
      else
	 send_state <= LsV2(s+1);
   endrule

   rule send_clear (send_state matches tagged Clear);
      $display("Sending clear:");
      lsv2.clear();
      send_state <= LsV2(8);
   endrule

   // Receive rules

   rule recv_Ls (recv_state matches tagged Ls .s);
      $display("16'hFFFF << 4'b%b = 16'b%b", s, tpl_2(ls.first));
      ls.deq();
      if (s == 15) begin
	 $display("Testing LsV2:");
	 recv_state <= LsV2(0);
      end
      else
	 recv_state <= Ls(s+1);
   endrule
   
   rule recv_LsV2 (recv_state matches tagged LsV2 .s);
      $display("16'hFFFF << 4'b%b = 16'b%b", s, tpl_2(lsv2.first));
      lsv2.deq();
      if (s == 15) begin
	 $display("Done");
	 $finish(0);
      end
      else
      // skip the cleared locations
      if (s == 3)
	 recv_state <= LsV2(8);
      else
	 recv_state <= LsV2(s+1);
   endrule
   
endmodule

