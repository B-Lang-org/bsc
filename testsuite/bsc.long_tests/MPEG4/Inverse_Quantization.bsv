/////////////////////////////////////////////////////////////////////////
/* Performs inverse quantization for AC coeff
   using both method I and II
*/

package Inverse_Quantization;

interface Inverse_Quantization_IFC;
  method Bit#(12) getmethod1(
                    Bit#(1) sign,
		            Bool isIntra,
					Bit#(12) dct_data,
					Bit#(16) qp,
					Bit#(8) quant_value);

  method Bit#(12) getmethod2(
                    Bit#(1) sign,
					Bit#(12) level,
					Bit#(16) qp);

  method Bit#(12) saturate(Bit#(16) value);
endinterface: Inverse_Quantization_IFC

function Bit#(16) func_getmethod1(Bit#(1) sign,Bool isIntra,Bit#(12) dct_data,Bit#(16) qp,Bit#(8) quant_value);
  Bit#(16) res;
  Bit#(16) k = isIntra ? 0 : ((sign == 1) ? 16'hffff : 16'h0000);
  Bit#(16) tmp_dct_data = signExtend(dct_data);
  Bit#(16) tmp = ({tmp_dct_data[14:0],1'b0} + k) * signExtend(quant_value) * signExtend(qp);
  Bit#(16) tmp1 = {tmp[15],tmp[15],tmp[15],tmp[15],tmp[15:4]};
  if (dct_data == 0)
	 res = 0;
  else
    res = tmp1; 
  return res;
endfunction

function Bit#(16) func_getmethod2(Bit#(1) sign,Bit#(12) level,Bit#(16) qp);
  Bit#(16) res;
  Bit#(16) tmp_level;
  Bit#(16) tmp ;
  Bit#(1)  tmp_sign;
  if (level[11] == 1)
    begin
      tmp_level = zeroExtend(~level + 1);
	  tmp_sign = 1;
    end
  else
    begin
      tmp_level = zeroExtend(level);
	  tmp_sign = sign;
    end
  tmp = ((tmp_level << 1) + 1) * qp;
  if (level == 0)
    res = 0;
  else
    begin
       Bit#(16) tmp1;
       if (qp[0] == 1)
          tmp1 = tmp;
       else
          tmp1 = tmp -1;
       res = (tmp_sign == 1) ? (~tmp1 + 1)  : tmp1;
    end
  return res;
endfunction

function Bit#(12) func_saturate (Bit#(16) value);
  Bit#(12) res;
  /*
  if (value < -2047)
    res = -2047;
  else if (value > 16'd2047)
    res = 2047;
  else
    res = truncate(value);
	*/
  if (value[15] == 1)
    begin
	  if (value < 16'h801)
	    res = 12'h801;
	  else
        res = value[11:0];
	end
  else
    begin
	  if (value > 16'd2047)
        res = 2047;
	  else
        res = value[11:0];
	end
  return(res);
endfunction

(* synthesize ,
   CLK = "clk",
   RST_N = "reset"
*)
module mkInverse_quantized(Inverse_Quantization_IFC);

  method getmethod1(sign,isIntra,dct_data,qp,quant_value);
    Bit#(16) tmp_result = func_getmethod1(sign,isIntra,dct_data,qp,quant_value);
	Bit#(12) saturated_result = func_saturate(tmp_result);
    getmethod1 = saturated_result;	
  endmethod: getmethod1

  method getmethod2(sign,level,qp);
    Bit#(16) tmp_result = func_getmethod2(sign,level,qp);
	Bit#(12) saturated_result = func_saturate(tmp_result);
    getmethod2 = saturated_result;	
  endmethod: getmethod2

  method saturate(value);
    saturate = func_saturate(value);
  endmethod: saturate

endmodule: mkInverse_quantized

endpackage : Inverse_Quantization
