import SVA::*;
import FPLibrary::*;
import FPAdd::*;
import TesterLib::*;

module mkFPAddAssert(QBinOp#(IEEE754_32));

  QBinOp #(IEEE754_32) dut();
  mkFPAdd i_dut(dut);
 
  QBinOp #(IEEE754_32) assert_dut();
  wrapAssert#(dut) i_assert_dut(assert_dut);
  
  return(assert_dut);
endmodule
  
module wrapAssert#(QBinOp#(IEEE754_32) op)(QBinOp#(IEEE754_32));

   let fpi_out = case (op.result) matches
                   tagged Valid .v : return (tagged Valid extract_fields(v));
                   tagged Invalid : return tagged Invalid;
                 endcase;   
       
   property hiddenBit(); 
      fpi_out matches tagged Valid .fpi &&& 
      (fpi.exp != 0) ? True : False |-> 
      topBit(fromMaybe(fpi_zero, fpi_out).sfd) == 1;
   endproperty

   always assert property(hiddenBit())
     $display("Time: %0t hiddenBit: PASS", $time);
   else $display("Time: %0t hiddenBit: FAIL", $time);

   method start = op.start;
   method result = op.result;
   method deq = op.deq;

endmodule

