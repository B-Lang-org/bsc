import List::*;
import SVA2::*;


interface Summer;
  method Action inp(int x);
  method int outp();
endinterface

module [Module] mkSimpleSummer (Summer);
  
  Reg#(int) pipe1 <- mkReg(0);
  Reg#(int) pipe2 <- mkReg(1);
  Reg#(int) pipe3 <- mkReg(2);
  Reg#(int) pipe4 <- mkReg(3);

  module assertion_1_8(Property);
	
          module assertion_1_1(Sequence);
            mkSeqExpr(pipe2 > 0);
          endmodule: assertion_1_1
        
	  let assertion_1_2 <- replicateM('d0000000001, assertion_1_1);
        
	  module assertion_1_5(Property);
            let assertion_1_3 <- mkSeqExpr(pipe1 > pipe2 || pipe1 < 0);
            mkPropSeq(assertion_1_3);
          endmodule: assertion_1_5
	  
          let assertion_1_6 <- replicateM('d0000000001, assertion_1_5);
	  
          mkPropImplies(assertion_1_2, assertion_1_6);
	  
  endmodule

  module assertion_2_8(Property);
	
          module assertion_2_1(Sequence);
            mkSeqExpr(pipe2 < 0);
          endmodule: assertion_2_1
	  
          let assertion_2_2 <- replicateM('d0000000001, assertion_2_1);
          
	  module assertion_2_5(Property);
            let assertion_2_3 <- mkSeqExpr(pipe1 < pipe2 || pipe1 > 0);
            mkPropSeq(assertion_2_3);
          endmodule: assertion_2_5
          
	  let assertion_2_6 <- replicateM('d0000000001, assertion_2_5);
          
	  mkPropImplies(assertion_2_2, assertion_2_6);
	  
  endmodule

  List#(Property) assertion_1_9 <- replicateM('d0000000001, assertion_1_8);
  Assertion assertion_0 <- mkAssertAlways(assertion_1_9, noAction, 
    $display("Warning: SimpleSummer inputs should grow or switch sign"));
    
  (* fire_when_enabled, no_implicit_conditions *)
  rule assertion_0_fire (True);
     Bool foo <- assertion_0.advance();
  endrule: assertion_0_fire


  List#(Property) assertion_2_9 <- replicateM('d0000000001, assertion_2_8);
  Assertion assertion_1 <- mkAssertAlways(assertion_1_9, noAction, 
     $display("Warning: SimpleSummer inputs should shrink or switch sign"));

  (* fire_when_enabled, no_implicit_conditions *)
  rule assertion_1_fire (True);
     Bool foo <- assertion_1.advance();
  endrule: assertion_1_fire

  method Action inp(int x);
    int tmp = x;
    if (x < 0) tmp = tmp - 4; 
      else tmp = tmp + 4;
    pipe1 <= tmp;
    pipe2 <= pipe1;
    pipe3 <= pipe2;
    pipe4 <= pipe3;
  endmethod
 
  method int outp();
    return pipe1 + pipe2 + pipe3 + pipe4;
  endmethod
endmodule

module [Module] mkTest (Empty);

  Summer sum <- mkSimpleSummer;
  Reg#(Int#(5)) r <- mkReg(0);
  
  rule gogo(True);
    r <= r + 5;
    sum.inp(zeroExtend(r));

    int res = sum.outp();
    $display("Res: %0d", res);
  endrule
  
endmodule
