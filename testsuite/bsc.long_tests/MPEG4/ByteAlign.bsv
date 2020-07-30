/////////////////////////////////////////////////////////////////////////
/* Performs byte alignment on a 8 bit input data and returns 8 bit data 
   and stores the residual value in input buffer 
*/

package ByteAlign;

interface ByteAlign_IFC;
  method Bit#(16) get(Bit#(40) input_reg,Bit#(5) byte_align_pos, Bit#(4) number);
  method Bit#(40) flushdata(Bit#(4) byte_align_pos,Bit#(40) input_reg);
  method Bit#(16) bs (Bit#(16) input_reg,Bit#(16) tmp, Bit#(4) offset);
endinterface: ByteAlign_IFC

function Bit#(16) func_bs (Bit#(16) input_reg,Bit#(16) tmp, Bit#(4) offset);
Bit#(16) res;
       case (offset)
	     4'b0000 : res = input_reg;
	     4'b0001 : res = {input_reg[14:0],tmp[0]};
	     4'b0010 : res = {input_reg[13:0],tmp[1:0]};
	     4'b0011 : res = {input_reg[12:0],tmp[2:0]};
	     4'b0100 : res = {input_reg[11:0],tmp[3:0]};
	     4'b0101 : res = {input_reg[10:0],tmp[4:0]};
	     4'b0110 : res = {input_reg[9:0],tmp[5:0]};
	     4'b0111 : res = {input_reg[8:0],tmp[6:0]};
	     4'b1000 : res = {input_reg[7:0],tmp[7:0]};
	     default : res = zeroExtend(input_reg); 
       endcase
   return res;
endfunction

function Bit#(40) func_flushdata (Bit#(4) pos,Bit#(40) in_data);
Bit#(40) res;
       case (pos)
	     4'b0000 : res = zeroExtend(in_data[7:0]); 
	     4'b0001 : res = zeroExtend(in_data[8:0]); 
	     4'b0010 : res = zeroExtend(in_data[9:0]);
	     4'b0011 : res = zeroExtend(in_data[10:0]);
	     4'b0100 : res = zeroExtend(in_data[11:0]);
	     4'b0101 : res = zeroExtend(in_data[12:0]);
	     4'b0110 : res = zeroExtend(in_data[13:0]);
	     4'b0111 : res = zeroExtend(in_data[14:0]);
	     default : res = zeroExtend(in_data); 
       endcase
   return res;
endfunction


function Bit#(16) func_get (Bit#(40) in_data,Bit#(5) byte_align_pos,Bit#(4) num);
   if ((byte_align_pos == 0) || (byte_align_pos < zeroExtend(num)))
      return in_data[15:0];
   else begin
      Nat top = zeroExtend(byte_align_pos - 1);
      Nat bot = zeroExtend(byte_align_pos - {1'b0,num});
      return in_data[top:bot];
   end
endfunction

(* synthesize ,
   CLK = "clk",
   RST_N = "reset"
*)
module mkByteAlign(ByteAlign_IFC);

  method get(input_reg,byte_align_pos,num);
    get = func_get(input_reg,byte_align_pos,num);
  endmethod: get

  method flushdata(byte_align_pos,input_reg);
    flushdata = func_flushdata(byte_align_pos,input_reg);
  endmethod: flushdata

  method bs(input_reg,tmp,offset);
    bs = func_bs(input_reg,tmp,offset);
  endmethod: bs

endmodule: mkByteAlign

endpackage : ByteAlign
