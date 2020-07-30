/*----------------------------------------------------------------------------

Testbench for Example4Q

The expected output is:

Testing Ls3:
8'hFF << 3'b000 = 8'b11111111
8'hFF << 3'b001 = 8'b11111110
8'hFF << 3'b010 = 8'b11111100
8'hFF << 3'b011 = 8'b11111000
8'hFF << 3'b100 = 8'b11110000
8'hFF << 3'b101 = 8'b11100000
8'hFF << 3'b110 = 8'b11000000
8'hFF << 3'b111 = 8'b10000000
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
Done
 
-----------------------------------------------------------------------------*/

import FIFO::*;
import Example4Q::*;

typedef union tagged {
   void    Start;
   Bit#(3) Ls3;
   Bit#(4) Ls;
   void    Done;	      
} State deriving (Eq, Bits);

module mkTb4 (Empty);

   // DUTs
   
   FIFO#(SXpair#(3,8)) ls3();
   mkLs3 the_ls3(ls3);

   FIFO#(SXpair#(4,16)) ls();
   mkLs the_ls(ls);

   // Testbench state
   
   Reg#(State) send_state();
   mkReg#(Start) send_state_r(send_state);

   Reg#(State) recv_state();
   mkReg#(Start) recv_state_r(recv_state);

   // Send rules

   rule send_start (send_state matches tagged Start);
      $display("Testing Ls3:");
      send_state <= Ls3(0);
      recv_state <= Ls3(0);
   endrule

   rule send_Ls3 (send_state matches tagged Ls3 .s);
      ls3.enq(tuple2(s, 8'hFF));
      if (s == 7)
	 send_state <= Ls(0);
      else
	 send_state <= Ls3(s+1);
   endrule

   rule send_Ls (send_state matches tagged Ls .s);
      ls.enq(tuple2(s, 16'hFFFF));
      if (s == 15)
	 send_state <= Done;
      else
	 send_state <= Ls(s+1);
   endrule

   // Receive rules

   rule recv_Ls3 (recv_state matches tagged Ls3 .s);
      $display("8'hFF << 3'b%b = 8'b%b", s, tpl_2(ls3.first));
      ls3.deq();
      if (s == 7) begin
	 $display("Testing Ls:");
	 recv_state <= Ls(0);
      end
      else
	 recv_state <= Ls3(s+1);
   endrule

   rule recv_Ls (recv_state matches tagged Ls .s);
      $display("16'hFFFF << 4'b%b = 16'b%b", s, tpl_2(ls.first));
      ls.deq();
      if (s == 15) begin
	 $display("Done");
	 $finish(0);
      end
      else
	 recv_state <= Ls(s+1);
   endrule
   
endmodule

