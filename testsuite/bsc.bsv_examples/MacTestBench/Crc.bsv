package Crc;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

import FIFO::*;
import GetPut::*;
import Vector::*;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface CrcCalculatorIFC;
   method Action initialize();
   method Bit#(32) getCrc();
   method Bit#(4) getFcs();      
   interface Put#(Maybe#(Bit#(4))) data;
endinterface   

(* synthesize *)     
module mkCrcCalculator (CrcCalculatorIFC);

   FIFO#(Maybe#(Bit#(4))) in_fifo <- mkFIFO;
   Reg#(Bit#(32)) crc <- mkReg(32'hFFFFFFFF);

   RWire#((Maybe#(Bit#(4))))  data_wire <- mkRWire;

   rule update_wire;

      data_wire.wset(in_fifo.first());
      
   endrule

   rule update_crc;
      
      let crc_next = calculateCrcNext(in_fifo.first(), crc);
      
      crc <= crc_next;
      
      in_fifo.deq();

   endrule

   method Action initialize();
      crc <= 32'hFFFFFFFF;
   endmethod

   method Bit#(32) getCrc();
      if (isValid(data_wire.wget()))
	 begin
	    let crc_next = calculateCrcNext(validValue(data_wire.wget()), crc);
	    return crc_next;
	 end
      else
	 return crc;
   endmethod

   method Bit#(4) getFcs();
      if (isValid(data_wire.wget()))
	 begin
	    let crc_next = calculateCrcNext(validValue(data_wire.wget()), crc);
	    return {~crc_next[28], ~crc_next[29], ~crc_next[30], ~crc_next[31]};
	 end
      else
	 return {~crc[28], ~crc[29], ~crc[30], ~crc[31]};
   endmethod

   interface Put data = fifoToPut(in_fifo);

endmodule



(* noinline *)      
function Bit#(32) calculateCrcNext(Maybe#(Bit#(4)) maybe_data, Bit#(32) crc);

   Bit#(32) crc_next;
   Bit#(4) data;
   Bit#(1) enable_value;

   if (isValid(maybe_data))
      begin
	 let tmp = validValue(maybe_data);
	 data = {tmp[0], tmp[1], tmp[2], tmp[3]};
	 enable_value = 'b1;
      end
   else
      begin
	 data = 0;
	 enable_value = 'b0;
      end

   crc_next[0] = enable_value & (data[0] ^ crc[28]); 
   crc_next[1] = enable_value & (data[1] ^ data[0] ^ crc[28] ^ crc[29]); 
   crc_next[2] = enable_value & (data[2] ^ data[1] ^ data[0] ^ crc[28] ^ crc[29] ^ crc[30]); 
   crc_next[3] = enable_value & (data[3] ^ data[2] ^ data[1] ^ crc[29] ^ crc[30] ^ crc[31]); 
   crc_next[4] = (enable_value & (data[3] ^ data[2] ^ data[0] ^ crc[28] ^ crc[30] ^ crc[31])) ^ crc[0]; 
   crc_next[5] = (enable_value & (data[3] ^ data[1] ^ data[0] ^ crc[28] ^ crc[29] ^ crc[31])) ^ crc[1]; 
   crc_next[6] = (enable_value & (data[2] ^ data[1] ^ crc[29] ^ crc[30])) ^ crc[ 2]; 
   crc_next[7] = (enable_value & (data[3] ^ data[2] ^ data[0] ^ crc[28] ^ crc[30] ^ crc[31])) ^ crc[3]; 
   crc_next[8] = (enable_value & (data[3] ^ data[1] ^ data[0] ^ crc[28] ^ crc[29] ^ crc[31])) ^ crc[4]; 
   crc_next[9] = (enable_value & (data[2] ^ data[1] ^ crc[29] ^ crc[30])) ^ crc[5]; 
   crc_next[10] = (enable_value & (data[3] ^ data[2] ^ data[0] ^ crc[28] ^ crc[30] ^ crc[31])) ^ crc[6]; 
   crc_next[11] = (enable_value & (data[3] ^ data[1] ^ data[0] ^ crc[28] ^ crc[29] ^ crc[31])) ^ crc[7]; 
   crc_next[12] = (enable_value & (data[2] ^ data[1] ^ data[0] ^ crc[28] ^ crc[29] ^ crc[30])) ^ crc[8]; 
   crc_next[13] = (enable_value & (data[3] ^ data[2] ^ data[1] ^ crc[29] ^ crc[30] ^ crc[31])) ^ crc[9]; 
   crc_next[14] = (enable_value & (data[3] ^ data[2] ^ crc[30] ^ crc[31])) ^ crc[10]; 
   crc_next[15] = (enable_value & (data[3] ^ crc[31])) ^ crc[11]; 
   crc_next[16] = (enable_value & (data[0] ^ crc[28])) ^ crc[12]; 
   crc_next[17] = (enable_value & (data[1] ^ crc[29])) ^ crc[13]; 
   crc_next[18] = (enable_value & (data[2] ^ crc[30])) ^ crc[14]; 
   crc_next[19] = (enable_value & (data[3] ^ crc[31])) ^ crc[15]; 
   crc_next[20] = crc[16]; 
   crc_next[21] = crc[17]; 
   crc_next[22] = (enable_value & (data[0] ^ crc[28])) ^ crc[18]; 
   crc_next[23] = (enable_value & (data[1] ^ data[0] ^ crc[29] ^ crc[28])) ^ crc[19]; 
   crc_next[24] = (enable_value & (data[2] ^ data[1] ^ crc[30] ^ crc[29])) ^ crc[20]; 
   crc_next[25] = (enable_value & (data[3] ^ data[2] ^ crc[31] ^ crc[30])) ^ crc[21]; 
   crc_next[26] = (enable_value & (data[3] ^ data[0] ^ crc[31] ^ crc[28])) ^ crc[22]; 
   crc_next[27] = (enable_value & (data[1] ^ crc[29])) ^ crc[23]; 
   crc_next[28] = (enable_value & (data[2] ^ crc[30])) ^ crc[24]; 
   crc_next[29] = (enable_value & (data[3] ^ crc[31])) ^ crc[25]; 
   crc_next[30] = crc[26]; 
   crc_next[31] = crc[27]; 

   return crc_next;

endfunction

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

function Bit#(32) calculateFCS(Bit#(32) crc);

   Vector#(8, Bit#(32)) crc_vector = newVector;
   Vector#(8, Bit#(4)) fcs_v = newVector;
   Bit#(32) fcs;
   Integer i;

   let value_first = crc;
   crc_vector[0] = value_first;
   fcs_v[0] = {~value_first[28], ~value_first[29], ~value_first[30], ~value_first[31]};
   
   for (i = 1; i < 8; i = i +1)
      begin
	 let value = calculateCrcNext(Nothing, crc_vector[i - 1]);
	 crc_vector[i] = value;
	 fcs_v[i] = {~value[28], ~value[29], ~value[30], ~value[31]};
      end
   
   fcs = {fcs_v[0], fcs_v[1], fcs_v[2], fcs_v[3], fcs_v[4], fcs_v[5], fcs_v[6], fcs_v[7]};
   
   return fcs;

endfunction
      

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

endpackage

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

