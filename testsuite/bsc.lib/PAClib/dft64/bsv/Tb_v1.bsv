
import ClientServer::*;
import GetPut::*;
import Complex::*;

import FixedPoint::*;
import Vector::*;
import StmtFSM::*;
import FShow::*;

import FixedPointIO::*;
import DFTCoef::*;
import DFT::*;
import DFT_v1::*;
import Real::*;

(*synthesize*)
module sysTb_v1();

   Reg#(UInt#(17)) i <- mkReg(0);
   Reg#(UInt#(10)) received <- mkReg(0);
   Server#(VData_t, VData_t) dut <- mkDFT_v1 ;

   Stmt fsm =
   (seq
       action
          let ifn = "Test.dat";
          let ofn = "Test_out_v1.dat.out";
          let x <- openreadfile(ifn);
          let y <- openwritefile(ofn);
          $display ("Opened input and output files: %s %s", ifn, ofn);
          //fxptWriteString("Coefficients: ------------------");  fxptWriteNewLine;
          //writePoints(coef_src);
          //fxptWriteString("------------------");  fxptWriteNewLine;
       endaction

       while (i < 10)
          seq
             action
                let mx <- readPoints();
                if (mx matches tagged Valid .x) begin
                   $display("Sending data set %d at %t", i, $time);

                   i <= i +1 ;
                   dut.request.put(x);
                end
                else begin
                   $display("Invalid data found");
                   i <= i + 100000;
                end
             endaction
          endseq
       // Wait to allow data to process
       i <= 0;
       while (i < 10000) seq i <= i + 1; endseq
    endseq);

   mkAutoFSM(fsm);

   rule readOutput ;
      received <= received + 1;
      $display ("received response %d at time", received, $time);
      VData_t dout <- dut.response.get;
      fxptWriteString ("response -----");     fxptWriteNewLine;
      writePoints (dout);
      fxptWriteString("------------------");     fxptWriteNewLine;
   endrule
endmodule


