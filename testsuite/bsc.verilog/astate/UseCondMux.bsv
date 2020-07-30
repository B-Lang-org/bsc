import RegFile::*;

typedef enum 
  { Rule1, Rule2, Rule3, Rule4, Exit }
  State deriving(Eq, Bits);

(* synthesize *)
module mkMyRegFile(RegFile#(Bit#(3), Bit#(3)));

  method upd(a, v);
    return(noAction);
  endmethod

  method sub(v);
    return(v);
  endmethod

endmodule

(* synthesize *)
module sysUseCondMux();

  Reg#(State) state  <- mkReg(Rule1);
  Reg#(State) state2 <- mkReg(Rule1);

  RegFile#(Bit#(3), Bit#(3)) data <- mkMyRegFile;

  rule rule1(state == Rule1);
    if(state2 == Rule1) begin
      $display("Rule 1 %0d", data.sub(0));
      state  <= Rule2;
      state2 <= Rule2;
    end
  endrule
  
  rule rule2(state == Rule2);
    if(state2 == Rule2) begin
      $display("Rule 2 %0d", data.sub(1));
      state  <= Rule3;
      state2 <= Rule3;
    end
  endrule
    
  rule rule3(state == Rule3);
    if(state2 == Rule3) begin
      $display("Rule 3 %0d", data.sub(0));
      state  <= Rule4;
      state2 <= Rule4;
    end
  endrule

  rule rule4(state == Rule4);
    $display("Rule 4 %0d", data.sub(1));
    state <= Exit;
  endrule
  
  rule exit(state == Exit);
    $display("Exit %0d", data.sub(0));
    $finish(0);
  endrule
  
endmodule               