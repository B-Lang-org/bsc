import FixedPoint::*;
import FixedPointLibrary::*;
import TypeClasses::*;

module mkTest(Empty);

   Reg#(Bit#(16))     fxptReg <- mkReg(0);
   Reg#(Bit#(18)) powerResReg <- mkReg(0);
   
   rule alwaysMult(True);
   begin
      // the following 2 lines don't  compile
      FixedPoint#(1,15)   fxptVal = unpack(fxptReg);
      FixedPoint#(2,16)  powerRes = grow(fxptVal);
      // the following 2 lines compile 
      // FixedPoint#(8,8)   fxptVal = unpack(fxptReg);
      // FixedPoint#(9,9)  powerRes = grow(fxptVal);
      // the following 2 lines also compile 
      // FixedPoint#(1,15)   fxptVal = unpack(fxptReg);
      // FixedPoint#(2,16)  powerRes = fxptSignExtend(fxptVal);
      fxptReg  <= fxptReg + 1024;
      powerResReg <= pack(powerRes);
   end
   endrule

endmodule
      


