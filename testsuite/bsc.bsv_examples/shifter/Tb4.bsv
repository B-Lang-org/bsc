import FIFO::*;
import Example4::*;

typedef union tagged {
   void    Start;
   Bit#(3) Ls3;
   Bit#(4) Ls;
   Bit#(4) LsV2;
   void    Done;	      
} State deriving (Eq, Bits);

module mkTb4 (Empty);

   // DUTs
   
   FIFO#(SXpair#(3,8)) ls3();
   mkLs3 the_ls3(ls3);

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
	 send_state <= LsV2(0);
      else
	 send_state <= Ls(s+1);
   endrule

   rule send_LsV2 (send_state matches tagged LsV2 .s);
      lsv2.enq(tuple2(s, 16'hFFFF));
      if (s == 15)
	 send_state <= Done;
      else
	 send_state <= LsV2(s+1);
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
	 recv_state <= LsV2(s+1);
   endrule
   
endmodule

