////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

package SDRAM;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

export ExtSDRAM(..);
export AddrSize(..);
export DataSize(..);
export mkSDRAM;

import FIFOF::*;
import ConfigReg::*;
import GetPut::*;
import ClientServer::*;
import RAM::*;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

typedef 25 AddrSize;
typedef 32 DataSize;

Bool bypassIFIFO;
bypassIFIFO = False;

interface ExtSDRAM;
   method Bool rd();
   method Bool wr();
   method Bit#(AddrSize) addr();
   method Bit#(DataSize) dIn();
   method Action dOut(Maybe#(Bit#(DataSize)) x1);
endinterface: ExtSDRAM

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

module mkSDRAM(Tuple2#(ExtSDRAM, RAM#(adr, dta)))
   provisos (Bits#(adr, adrs),
	     Add#(adrs, na, AddrSize),
	     Add#(na, adrs, AddrSize),
	     Bits#(dta, dtas),
	     Add#(dtas, nd, DataSize),
	     Add#(nd, dtas, DataSize),
	     Bits#(RAMreq#(Bit#(adrs), Bit#(dtas)), nr));
   
   let ifc <- (liftModule(module#(Tuple2#(ExtSDRAM, RAM#(adr, dta)));
		  FIFOF#(RAMreq#(Bit#(adrs), Bit#(dtas))) ififo();
		  mkFIFOF1 theififo(ififo);
		  FIFOF#(Bit#(dtas)) ofifo();
		  mkFIFOF1 theofifo(ofifo);
		  Reg#(Bool) doRD();
		  mkConfigReg#(False) thedoRD(doRD);
		  Reg#(Bool) doWR();
		  mkConfigReg#(False) thedoWR(doWR);
		  Reg#(Bit#(adrs)) oAddr();
		  mkConfigRegU theoAddr(oAddr);
		  Reg#(Bit#(dtas)) oData();
		  mkConfigRegU theoData(oData);
		  function setupCycle(x);
	             return (begin case (x) matches
				      tagged Read {.a} : 
					 (action
					     oAddr <= a;
					     doRD <= True;
					     doWR <= False;
					  endaction);
				      tagged Write {.a,.d} : 
					 (action
					     oAddr <= a;
					     oData <= d;
					     doRD <= False;
					     doWR <= True;
					  endaction);
				   endcase end);
		  endfunction: setupCycle
		  function packReq(x);
	             return (begin case (x) matches
				      tagged Read {.a} :  (Read (pack(a)));
				      tagged Write {.a,.d} :  (Write (tuple2(pack(a), pack(d))));
				   endcase end);
		  endfunction: packReq
		  let newCycle = 
		  action
		     ififo.deq;
		     setupCycle(ififo.first);
		  endaction;
		  rule dummy_name
		     (ififo.notEmpty && !(doRD) && !(doWR)); newCycle;
		  endrule
		  return(tuple2(interface ExtSDRAM
				   method rd() ;   return (doRD);
				   endmethod: rd
				   method wr() ;   return (doWR);
				   endmethod: wr
				   method addr() ;   return (zeroExtend(oAddr));
				   endmethod: addr
				   method dIn() ;   return (zeroExtend(oData));
				   endmethod: dIn
				   method dOut(x) ;
				      return (begin case (x) matches
						       tagged Invalid :  (noAction);
						       tagged Valid {.d} : 
							  (doRD ?
							   ofifo.notFull ?
							   action
							      (ofifo.enq)(truncate(d));
							      (ififo.notEmpty ?
							       newCycle
							       :   action
								      doRD <= False;
								      doWR <= False;
								   endaction);
							   endaction
							   :   noAction
							   :   ififo.notEmpty ?
							   newCycle
							   :   action
								  doRD <= False;
								  doWR <= False;
							       endaction);
						    endcase end);
				   endmethod: dOut
				endinterface: ExtSDRAM,
				interface Server
				   method request() ;
				      return (interface Put
						 method put(req) if (ififo.notFull) ;
					            let preq =  packReq(req);
					            return (!(bypassIFIFO) || ififo.notEmpty || doRD || doWR ?
							    (ififo.enq)(preq)
							    :   setupCycle(preq));
						 endmethod: put
					      endinterface: Put);
				   endmethod: request
				   method response() ;
				      return (interface Get
						 method get() if (ofifo.notEmpty) ;
					            return (actionvalue
							       ofifo.deq;
							       return(unpack(ofifo.first));
							    endactionvalue);
						 endmethod: get
					      endinterface: Get);
				   endmethod: response
				endinterface: Server));
	       endmodule));
   return(ifc);
endmodule: mkSDRAM

//  (* module_type = "Module", synthesize, always_ready, always_enabled *)
//  module foo(ExtSDRAM);
//     Tuple2#(ExtSDRAM, RAM#(Bit#(21), Bit#(32))) eram_ram();
//     mkSDRAM theeram_ram(eram_ram);
//     let eram =  eram_ram.fst;
//     let ram =  eram_ram.snd;
//     Reg#(Bool) wr();
//     mkRegU thewr(wr);
//     Reg#(Bit#(32)) x();
//     mkRegU thex(x);
//     Reg#(Bit#(32)) d();
//     mkRegU thed(d);
//     Reg#(Bit#(21)) wa();
//     mkRegU thewa(wa);
//     Reg#(Bit#(21)) ra();
//     mkRegU thera(ra);
//     rule dummy_name
//        (wr); (ram.request.put)(Write (tuple2(wa, d)));
//     endrule
//     rule dummy_name
//        (!(wr)); (ram.request.put)(Read (ra));
//     endrule
//     rule dummy_name
//        (True);
//        Bit#(32) xx;
//        xx <- ram.response.get;
//        x <= xx;
//     endrule
//     return(eram);
//  endmodule: foo

endpackage: SDRAM

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

