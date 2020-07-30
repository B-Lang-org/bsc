import SVA::*;
import FPLibrary::*;
import FPAdd::*;
import TesterLib::*;
import AssertionWires::*;

(* synthesize *) 
module [Module] mkFPAddAssertWires(AssertIfc#(QBinOp#(IEEE754_32), 1));

  QBinOp #(IEEE754_32) dut();
  mkFPAdd i_dut(dut);
 
  AssertIfc#(QBinOp#(IEEE754_32), 1) assert_dut();
  exposeAssertionWires#(wrapAssert(dut)) i_assert_dut(assert_dut);
  
  return(assert_dut);
endmodule
  
module [AssertModule] wrapAssert#(QBinOp#(IEEE754_32) op)(QBinOp#(IEEE754_32));

   AssertionReg a();
   mkAssertionReg#(0) i_a(a);

   let fpi_out = case (op.result) matches
                   tagged Valid .v : return (tagged Valid extract_fields(v));
                   tagged Invalid : return tagged Invalid;
                 endcase;   
       
   property hiddenBit(); 
      (fpi_out matches tagged Valid .fpi &&& 
      (fpi.exp != 0) ? True : False) |-> 
      (topBit(fromMaybe(fpi_zero, fpi_out).sfd) == 1);
   endproperty

   always assert property(hiddenBit())
   else a.set;

   method start = op.start;
   method result = op.result;
   method deq = op.deq;

endmodule

