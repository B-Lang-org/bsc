// The MIT License

// Copyright (c) 2006-2007 Massachusetts Institute of Technology

// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:

// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.

// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
// THE SOFTWARE.
import GetPut::*;
import H264Types::*;
import RegFile::*;

typedef enum 
{
  Forwarding,
  DumpingY,
  DumpingU,
  DumpingV
}
  State deriving (Bits, Eq);

module mkDeblockTee#(Get#(DeblockFilterOT) inputData, Put#(DeblockFilterOT) outputData, String prefix, Bool recordFrames) ();

 Reg#(Bit#(32)) cycles <- mkReg(0);
 Reg#(State) state <- mkReg(Forwarding);
 Reg#(Bit#(32)) horCounter;
 Reg#(Bit#(32)) verCounter;
 Reg#(Bit#(32)) counter; 
 Reg#(Bit#(PicWidthSz))  picWidth;
 Reg#(Bit#(PicHeightSz)) picHeight;
 Reg#(Bit#(PicAreaSz))   frameinmb;
 RegFile#(Bit#(TAdd#(PicAreaSz,6)), Bit#(32)) yValues;
 RegFile#(Bit#(TAdd#(PicAreaSz,4)), Bit#(32)) uValues;
 RegFile#(Bit#(TAdd#(PicAreaSz,4)), Bit#(32)) vValues;  
 
 if(recordFrames)
   begin
     counter <- mkReg(0);
     horCounter <- mkReg(0);
     verCounter <- mkReg(0); 
     picWidth  <- mkReg(maxPicWidthInMB);
     picHeight <- mkReg(0);
     frameinmb <- mkReg(0);
     yValues <- mkRegFileFull();
     uValues <- mkRegFileFull();
     vValues <- mkRegFileFull();    
   end


 rule cycleup;
   cycles <= cycles + 1;
 endrule

 rule processData(state == Forwarding);
   let dataIn <- inputData.get();
   outputData.put(dataIn); 
   $write(prefix);
   case (dataIn) matches
     tagged DFBLuma .data:
       begin 	
         $display("DFBLuma(%d): hor: %d ver:%d data:%h\n", cycles,data.hor, data.ver, data.data);
         if(recordFrames)
           begin
	     Bit#(TAdd#(PicAreaSz,6)) addr = {(zeroExtend(data.ver)*zeroExtend(picWidth)),2'b00}+zeroExtend(data.hor);
             $write(prefix);
             $display("Writing to %d, %h", addr, data);
             yValues.upd(addr,{data.data[7:0],data.data[15:8],data.data[23:16],data.data[31:24]});
           end 
       end
     tagged DFBChroma .data:
       begin 
         $display("DFBChroma(%d): flag: %d hor: %d ver:%d data:%h\n", cycles, data.uv, data.hor, data.ver, data.data);
	 if(recordFrames)
           begin
             Bit#(TAdd#(PicAreaSz,4)) addr = {(zeroExtend(data.ver)*zeroExtend(picWidth)),1'b0}+zeroExtend(data.hor);
             if(data.uv == 1)
               begin
                 $write(prefix);
                 $display("Writing to %d, %h", addr, data);
	         vValues.upd(addr, {data.data[7:0],data.data[15:8],data.data[23:16],data.data[31:24]});
               end
             else
               begin
                 $write(prefix);
                 $display("Writing to %d, %h", addr, data);
                 uValues.upd(addr, {data.data[7:0],data.data[15:8],data.data[23:16],data.data[31:24]});
               end
           end
       end
     tagged EndOfFrame:
       begin
         if(recordFrames)
           begin 
             state <= DumpingY;
             counter <= 0;
           end
           $display("EndOfFrame(%d)", cycles);
       end
     tagged EDOT .data:
       case (data) matches 
         tagged SPSpic_width_in_mbs .xdata :
	   begin
             if(recordFrames)
               begin
                 picWidth <= xdata;
               end
           end
         tagged SPSpic_height_in_map_units .xdata :
           begin 
             if(recordFrames)
               begin
                 picHeight <= xdata;
	         frameinmb <= zeroExtend(picWidth)*zeroExtend(xdata);
               end
           end
       endcase
   endcase
 endrule

if(recordFrames)
 begin
   rule dumpY(state == DumpingY);
     Bit#(TAdd#(PicAreaSz,6)) addr = truncate({(verCounter*zeroExtend(picWidth)),2'b00}+zeroExtend(horCounter));
     $write(prefix);
     //$write("(%d,%d,%d,%d,%d,%d)", counter, addr, horCounter, verCounter, picWidth, picHeight);
     $write("DUMP ");
     $display("%h", yValues.sub(addr));
  
     yValues.upd(addr,0);    
     if(horCounter + 1 == zeroExtend(picWidth)*4) // 4 values per Mb
       begin
         horCounter <= 0;
         if(verCounter + 1 == zeroExtend(picHeight)*16)
           begin
             state <= DumpingU;
             verCounter <= 0;
             counter <= 0;
           end
         else
           begin
             verCounter <= verCounter + 1;
             counter <= counter + 1;
           end
       end  
     else
       begin
         horCounter <= horCounter + 1;
         counter <= counter + 1;
       end
   endrule

   rule dumpU(state == DumpingU);
     Bit#(TAdd#(PicAreaSz,4)) addr = truncate({(verCounter*zeroExtend(picWidth)),1'b0}+zeroExtend(horCounter));
     $write(prefix);
     //$write("(%d,%d,%d,%d)", counter, addr, horCounter, verCounter);

     $write("DUMP ");
     $display("%h", uValues.sub(addr));
     uValues.upd(addr, 0);  

     if(horCounter + 1 == zeroExtend(picWidth)*2) // 2 values per Mb
       begin
         horCounter <= 0;
         if(verCounter + 1 == zeroExtend(picHeight)*8) // Chroma have half as much data
           begin
             state <= DumpingV;
             verCounter <= 0;
             counter <= 0;
           end
         else
           begin
             verCounter <= verCounter + 1;
             counter <= counter + 1;
           end
       end  
     else
       begin
         horCounter <= horCounter + 1;
         counter <= counter + 1;
       end 
   endrule 

   rule dumpV(state == DumpingV);
     Bit#(TAdd#(PicAreaSz,4)) addr = truncate({(verCounter*zeroExtend(picWidth)),1'b0}+zeroExtend(horCounter));
     $write(prefix);
     //$write("(%d,%d,%d,%d)", counter, addr, horCounter, verCounter);
     $write("DUMP ");
     $display("%h", vValues.sub(addr));
     vValues.upd(addr, 0);  
     if(horCounter + 1 == zeroExtend(picWidth)*2) // 2 values per Mb
       begin
         horCounter <= 0;
         if(verCounter + 1 == zeroExtend(picHeight)*8) // Chroma have half as much data
           begin
             state <= Forwarding;
             verCounter <= 0;
           end
         else
           begin
             verCounter <= verCounter + 1;
             counter <= counter + 1;
           end
       end  
     else
       begin
         horCounter <= horCounter + 1;
         counter <= counter + 1;
       end
   endrule 
 end
endmodule

 
