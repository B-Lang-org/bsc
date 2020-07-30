import Real::*;
import FloatingPoint::*;
import StmtFSM::*;
import FShow::*;
import DefaultValue::*;
import Vector::*;
import GetPut::*;
import FIFO::*;
import ClientServer::*;

(* synthesize *)
module sysPipeMult();
   Server#(Tuple2#(Bit#(56), Bit#(56)), Bit#(112)) mMult <- mkGeneralPipelinedMultiplier;

   Reg#(int) reqcount <- mkReg(0);
   Reg#(int) respcount <- mkReg(0);

   rule get_result;
      let result <- mMult.response.get;
      $display("Result (%d): %d", respcount, result);
      respcount <= respcount + 1;
   endrule
   
   function Action doMult(Bit#(56) opA, Bit#(56) opB);
      action
         mMult.request.put(tuple2(opA,opB));
         $display("Request (%d): %d * %d", reqcount, opA, opB);
         reqcount <= reqcount + 1;
      endaction
   endfunction
      
   Stmt test =
   seq
      delay(10);
      // 0 * 0
      doMult(3, 5);
      doMult(100, 100);
      doMult(9, 6);
      doMult(1, 10000);
      doMult(12, 12);
      delay(20);

      // 0 * 18
      doMult(3, 'h3FFFF);
      doMult(100, 'h2ABCD);
      doMult(9, 'h3009C);
      doMult('h1FFFF, 'h3FFFF);
      delay(20);
      
      // 0 * 25
      doMult(3, 'h1FFFFFF);
      doMult(100, 'h1ABCDEF);
      doMult(9, 'h1000D5C);
      doMult('hFFFFFF, 'h1FFFFFF);
      delay(20);

      // 0 * 35
      doMult(3, 'h7FFFFFFFF);
      doMult(100, 'h5ABCDEF98);
      doMult(9, 'h60000563D);
      doMult('h3FFFFFFFF, 'h7FFFFFFFF);
      doMult(987654321, 12345678);
      doMult('h1FFFFFF, 'h4FFFF);
      doMult('h1FFFFFF, 'h4FFFFFFFF);
      doMult('h1FFFFFF, 'h1FFFFFFFFFFFFF);
      doMult('h7FFFFFFFFFFFFF, 'h03FFFFFFFFFFFF);
      delay(1000);
   endseq;
   
   mkAutoFSM(test);
   
endmodule

