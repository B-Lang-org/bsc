package Testbench ;

import Design::*;

typedef enum {Start , Wait1 , Sig1 , Sig2 , Sig3 , Sig4 , Sig5 , Sig6 , Sig7 , Sig8 , Sig9 , Sig10 , Wait_500 , Sig12 , Sig13 , Sig14 , Sig15} State deriving (Eq, Bits);


module mkTestbench(Empty);

	Design_IFC top <- mkDesign;

    Reg #(Bit#(8)) counter <- mkReg(0);
    Reg #(Bit#(16)) count_wait <- mkReg(0);
    Reg #(Bit#(8)) count_sig2_state <- mkReg(0);
    Reg #(Bit#(8)) count_sig3_state <- mkReg(0);
    Reg #(Bit#(8)) count_sig4_state <- mkReg(0);
    Reg #(Bit#(8)) count_sig5_state <- mkReg(0);
    Reg #(Bit#(8)) count_sig6_state <- mkReg(0);
    Reg #(Bit#(8)) count_sig7_state <- mkReg(0);

    Reg #(State) state <- mkReg(Start);

    Reg #(TLstates) hwy_sig <- mkReg(GREEN);
    Reg #(TLstates) frm_sig <- mkReg(GREEN);
    Reg #(Bit#(5)) long_timer_value <- mkReg(05);
    Reg #(Bit#(5)) short_timer_value <- mkReg(02);


   rule first (state == Start);
      action 
         top.tlc (False, long_timer_value, short_timer_value);
         state <= Sig1;
      endaction 
   endrule

   rule sig1_state (state == Sig1);
      action 
         top.tlc (True, long_timer_value, short_timer_value);
         state <= Sig2 ;
         $display("Car present on Farm Road ");
      endaction 
   endrule

   rule sig2_state (state == Sig2); 
      action 
         top.tlc (True, long_timer_value, short_timer_value);
         if (hwy_sig == YELLOW) begin
            $display("hwy_light turns Yellow ");
            state <= Sig3 ;
         end else if (count_sig2_state < 6) begin
            hwy_sig <= top.hwy_light ;
            count_sig2_state <= count_sig2_state + 1;                  
            $display("Waiting for hwy_light to turn Yellow " );
            state <= Sig2;
         end else begin
            $display("Waiting for TOO long : Testcase failed ");
            $finish(2'b00) ;
         end
      endaction 
   endrule

   rule sig3_state (state == Sig3); 
      action 
         top.tlc (True, long_timer_value, short_timer_value);
         if (hwy_sig == RED) begin
            $display("hwy_light turns Red ");
            state <= Sig4 ;
         end else if (count_sig3_state < 3) begin
            hwy_sig <= top.hwy_light ;
            count_sig3_state <= count_sig3_state + 1;                  
            $display("Waiting for hwy_light to turn Red " );
            state <= Sig3;
         end else begin
            $display("Waiting for TOO long : Testcase failed ");
            $finish(2'b00) ;
         end
      endaction 
              
   endrule

   rule sig4_state (state == Sig4);
      action
         top.tlc (True, long_timer_value, short_timer_value);
         if (frm_sig == GREEN) begin
            $display("farm_light turns Green ");
            state <= Sig5 ;
         end else if (count_sig4_state < 1) begin
            frm_sig <= top.farm_light ;
            count_sig4_state <= count_sig4_state + 1;                  
            $display("Waiting for farm_light to turn Green " );
            state <= Sig4;
         end else begin
            $display("Waiting for TOO long : Testcase failed ");
            $finish(2'b00) ;
         end
      endaction
   endrule

   rule sig5_state (state == Sig5);
      action
         top.tlc (True, long_timer_value, short_timer_value);
         if (frm_sig == YELLOW) begin
            $display("farm_light turns Yellow ");
            state <= Sig6 ;
         end else if (count_sig5_state < 6) begin
            frm_sig <= top.farm_light ;
            count_sig5_state <= count_sig5_state + 1;                  
            $display("Waiting for farm_light to turn Yellow ") ;
            state <= Sig5;
         end else begin
            $display("Waiting for TOO long : Testcase failed ");
            $finish(2'b00) ;
         end
      endaction
   endrule
              
   rule sig6_state (state == Sig6);
      action
         top.tlc (True, long_timer_value, short_timer_value);
         if (frm_sig == RED) begin 
            $display("farm_light turns Red ");
            state <= Sig7 ;
         end else if (count_sig6_state < 3) begin
            frm_sig <= top.farm_light ;
            count_sig6_state <= count_sig6_state + 1;                  
            $display("Waiting for farm_light to turn Red ");
            state <= Sig6;
         end else begin
            $display("Waiting for TOO long : Testcase failed ");
            $finish(2'b00) ;
         end
      endaction
   endrule
              
   rule sig7_state (state == Sig7);
      action
         top.tlc (True, long_timer_value, short_timer_value);
         if (hwy_sig == GREEN) begin
             $display("hwy_light turns Green ");
             $display("Simulation Passes ");
             $finish(2'b00) ;
         end else if (count_sig7_state < 1) begin
             hwy_sig <= top.hwy_light ;
             count_sig7_state <= count_sig7_state + 1;                  
             $display("Waiting for hwy_light to turn Green " );
             state <= Sig7;
         end else begin
             $display("Waiting for TOO long : Testcase failed ");
             $finish(2'b00) ;
         end
      endaction
   endrule

endmodule: mkTestbench
endpackage: Testbench
