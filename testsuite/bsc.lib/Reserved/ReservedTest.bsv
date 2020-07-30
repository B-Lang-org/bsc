import StmtFSM::*;
import Reserved::*;
import DefaultValue::*;

typedef struct {
		Bit#(8)      data1;
		Reserved#(4) data2;
		Bit#(4)      data3;
		} TestReserved deriving (Bits, Eq, Bounded);

typedef struct {
		Bit#(8)      data1;
		ReservedZero#(4) data2;
		Bit#(4)      data3;
		} TestZero deriving (Bits, Eq, Bounded);

typedef struct {
		Bit#(8)      data1;
		ReservedOne#(4) data2;
		Bit#(4)      data3;
		} TestOne deriving (Bits, Eq, Bounded);


module sysReservedTest();
   Reg#(TestReserved) t1 <- mkReg(unpack(0));
   Reg#(TestZero)     t2 <- mkReg(unpack(0));
   Reg#(TestOne)      t3 <- mkReg(unpack(0));
   
   Stmt test =
   seq
      delay(10);
      t1 <= unpack(16'hFFFF);
      $display("%x", t1);
      t2 <= unpack(16'hFFFF);
      $display("%x", t2);
      t3 <= unpack(16'hFFFF);
      $display("%x", t3);

      t1 <= unpack(16'h0000);
      $display("%x", t1);
      t2 <= unpack(16'h0000);
      $display("%x", t2);
      t3 <= unpack(16'h0000);
      $display("%x", t3);

      t1 <= unpack(16'hAAAA);
      $display("%x", t1);
      t2 <= unpack(16'hAAAA);
      $display("%x", t2);
      t3 <= unpack(16'hAAAA);
      $display("%x", t3);
   endseq;
   
   mkAutoFSM(test);
   
endmodule
