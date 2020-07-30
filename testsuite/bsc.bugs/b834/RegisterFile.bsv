package RegisterFile;

import List::*;
import Vector::*;
import FIFO::*;

import UNUM::*;
import PPC_Datatypes::*;
import ConfigReg::*;

//Separately compilable register file
(* synthesize *)
module mkRegisterFileFixed_3_2 (RegisterFile#(RegAddress, 
      	      	      	      	      	    Bit#(64), 
					    3, 
					    2));

    RegisterFile#(RegAddress, Bit#(64), 3, 2) r <- mkRegisterFileFixed();


    method Action readReg_Action(PluriBUS#(RegAddress, 3) x);
    
      r.readReg_Action(x);
      
    endmethod


    method PluriBUS#(Bit#(64), 3) readReg_Value(PluriBUS#(RegAddress, 3) x);
    
      return r.readReg_Value(x);
      
    endmethod


    method Action writeReg(PluriBUS#(Tuple2#(RegAddress, Bit#(64)), 2) x);
    
      r.writeReg(x);
      
    endmethod


    method Action flush();
    
      r.flush();
      
    endmethod

endmodule


//Generalized Register File
module mkRegisterFileFixed (RegisterFile#(RegAddress, 
      	      	      	      	     rdata_t, 
				     read_w, 
				     write_w))
    provisos 
             (Bits#(rdata_t,sa),
              Literal#(rdata_t));
   
    List#(RegAddress) addrlist = List::map(fromInteger,upto(0,83 - 1 ));
    List#(Reg#(rdata_t)) rs <- List::mapM(constFn(mkConfigReg(0)), addrlist);
   
    // Some how the number needs to vary based on raddr_t

    function rread(x);

      case (x) matches
	tagged Nothing:
          return Nothing;
	tagged Just .z:
          return Just ((List::select(rs, z))._read);
      endcase

    endfunction

    //findLast
    function Maybe#(rdata_t) findLast(List#(Maybe#(Tuple2#(RegAddress,rdata_t))) x,
                        	RegAddress addr);
      case (decodeList(x)) matches
	 tagged Nothing: return(Nothing);
	 tagged Just {.hd, .tl}:
	 begin
	   
           match {.laddr,.lval} = unJust(hd);
	   
           return ((isJust(hd) && (laddr == addr)) ?
                	Just(lval): findLast(tl,addr));
			
         end
      endcase
      
    endfunction

    //rwrite
    function Action rwrite(PluriBUS#(Tuple2#(RegAddress,rdata_t), in_w) x, RegAddress addr);
     action
     
      let maybe_val = findLast(toList(x),addr);
      let theReg = (List::select(rs, addr));
      
      noAction;
      
      case (maybe_val) matches
	tagged    Nothing: noAction;
	tagged Just(.val): theReg <= val;
      endcase
      
     endaction
    endfunction

    //readReg_Action
    method Action readReg_Action(PluriBUS#(RegAddress, read_w) x);
    
       noAction;
       
    endmethod


    //readReg_Value
    method PluriBUS#(rdata_t, read_w) readReg_Value(PluriBUS#(RegAddress, read_w) x);

      return (map(rread, x));

    endmethod


    //writeReg
    method Action writeReg(PluriBUS#(Tuple2#(RegAddress, rdata_t), write_w) x);
    
      function Action write(RegAddress addr);
       action
	 rwrite(x,addr);
       endaction
      endfunction
      
      List::joinActions(List::map(write, addrlist));

    endmethod


    //flush
    method Action flush();
    
      noAction;
      
    endmethod

endmodule

endpackage
