//----------------------------------------------------------------------//
// The MIT License 
// 
// Copyright (c) 2007 Alfred Man Cheuk Ng, mcn02@mit.edu 
// 
// Permission is hereby granted, free of charge, to any person 
// obtaining a copy of this software and associated documentation 
// files (the "Software"), to deal in the Software without 
// restriction, including without limitation the rights to use,
// copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the
// Software is furnished to do so, subject to the following conditions:
// 
// The above copyright notice and this permission notice shall be
// included in all copies or substantial portions of the Software.
// 
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
// OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
// HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
// WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
// FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
// OTHER DEALINGS IN THE SOFTWARE.
//----------------------------------------------------------------------//

//////////////////////////////////////////////////////////
// Interface: EHRReg#(sz, data_t)
// Description: create a EHRReg of data_t with sz read 
//              and write ports, the scheduling is
//              read0 < write0 < read1 < write1 < ....
//
// Module: mkEHRReg(data_t init)
// Description: create the EHRReg with init as initial value              
/////////////////////////////////////////////////////////

import Vector::*;

interface VRead#(type a);
   method a read();
endinterface

interface EHR#(type a);
   interface VRead#(a) vRead; 
   interface Reg#(a)   vReg;
endinterface
  
typedef Vector#(sz, Reg#(a)) EHRReg#(numeric type sz, type a);

module mkVRead#(Reg#(a) first)
  (VRead#(a)) provisos (Bits#(a,asz));

   method a read();
     return first;
   endmethod
   
endmodule // mkVRead


module mkEHR#(VRead#(a) last) 
  (EHR#(a)) provisos (Bits#(a,asz));

   RWire#(a) rwire <- mkRWire;

   interface VRead vRead;
      method a read();
         let res = (isValid(rwire.wget)) ? 
		   fromMaybe(?,rwire.wget) :
		   last.read;
         return res;
      endmethod
   endinterface 	
     
   interface Reg vReg;
      method Action _write(a x);
         rwire.wset(x);
      endmethod
	
      method a _read();
         return last.read;
      endmethod
   endinterface 	
endmodule

module mkEHRReg#(a init) (EHRReg#(sz,a)) provisos (Bits#(a,asz));

   Reg#(a)             dataReg <- mkReg(init);
   VRead#(a)          fstVRead <- mkVRead(dataReg);
   Vector#(sz, EHR#(a)) ehrs = newVector;
   EHRReg#(sz, a)     ehrReg = newVector;
   ehrs[0]  <- mkEHR(fstVRead);
   ehrReg[0] = ehrs[0].vReg;
   for(Integer i = 1; i < valueOf(sz); i = i + 1)
   begin
      ehrs[i]  <- mkEHR(ehrs[i-1].vRead);
      ehrReg[i] = ehrs[i].vReg;
   end

   rule updateReg(True);
      dataReg <= ehrs[valueOf(sz)-1].vRead.read;
   endrule
   
   return ehrReg;
endmodule // mkEHRReg

module mkXReg#(a init) (Reg#(a)) provisos (Bits#(a,asz));

   //Reg#(a)             dataReg <- mkReg(init);
   rule updateReg(True);
      $display("XXX");
   endrule
   
   return ?;// dataReg;
endmodule // mkEHRReg




(*synthesize*)
(* options = "-elab -keep-fires"*)
module sysEHRReg ( );
   Vector#(3,Reg#(Bit#(5))) xxx <- replicateM(mkXReg(0));
   
   (*preempts = "xxx_1_updateReg, r2" *)
   rule r2 (True);
      $display(" r2");
   endrule
   
endmodule
