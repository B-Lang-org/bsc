package StatefulWallace;

// Defines three kinds of stateful Wallace adders.
// Each has a single internal register holding
// the intermediate result of the Wallace algorithm
// at every step. They differ in the predicate
// used to control the internal processing.
// This could have been factored out, but was not in 
// order to keep the example simpler.

import WallaceLib::*;

import WallaceServer::*;

import ClientServer::*;

import GetPut::*;

import ListN::*;

function Bool done(ListN#(n,Bit1) l) provisos(Add#(1,q,n));
  return(pack(tail(l)) == 0);
endfunction: done

// Add#(m,k,n) indicates that the result must have as many or more bits
// as the l input numbers
// Add#(1,q,l) indicates that at least one input number must be provided
// (i.e. l >= 1).  
module mkStatefulWallace1(WallaceServer#(l,m,n)) provisos (Add#(m,k,n), Add#(1,q,l));
  
  Reg#(ListN#(n,ListN#(l, Bit1))) state();
  // mkRegU is used because the initial value of the state does not matter
  mkRegU the_state(state); 

  // is the adder busy processing (is the data in state valid)?
  Reg#(Bool) busy();
  mkReg#(False) the_busy(busy);

  // process unconditionally
  rule wallaceStep (True);
    action
      ListN#(n,List#(Bit1)) x = map(toList,state);
      state <= map(padListToListN,statefulWallaceStep(x));
    endaction
  endrule: wallaceStep    

  method request();
    return (interface Put;
	      method put(inlistn) if (busy == False()); 
                  return(action 
                            state <= transpose(map(compose(padToNBits,unpack),inlistn));
                            busy  <= True();
                         endaction);
	      endmethod: put
	    endinterface: Put);
  endmethod: request

  method response(); return (interface Get;
                               method get() if ((busy == True()) && 
                                                (all(done,state)));
                                 actionvalue 
                                   busy <= False();
                                   return(pack(map(compose(head0,toList),state)));
                                 endactionvalue 
                               endmethod: get
                             endinterface: Get);
  endmethod: response

endmodule: mkStatefulWallace1

  
module mkStatefulWallace2(WallaceServer#(l,m,n)) provisos (Add#(m,k,n), Add#(1,q,l));
  
  Reg#(ListN#(n,ListN#(l, Bit1))) state();
  mkRegU the_state(state); 

  Reg#(Bool) busy();
  mkReg#(False) the_busy(busy);

  // process only when the data is valid
  rule wallaceStep (busy);
    action
      ListN#(n,List#(Bit1)) x = map(toList,state);
      state <= map(padListToListN,statefulWallaceStep(x));
    endaction
  endrule: wallaceStep    

  method request();
    return (interface Put;
	      method put(inlistn) if (busy == False()); 
                  return(action 
                            state <= transpose(map(compose(padToNBits,unpack),inlistn));
                            busy  <= True();
                         endaction);
	      endmethod: put
	    endinterface: Put);
  endmethod: request

  method response(); return (interface Get;
                               method get() if ((busy == True()) && 
                                                (all(done,state)));
                                 actionvalue 
                                   busy <= False();
                                   return(pack(map(compose(head0,toList),state)));
                                 endactionvalue 
                               endmethod: get
                             endinterface: Get);
  endmethod: response

endmodule: mkStatefulWallace2

  
module mkStatefulWallace3(WallaceServer#(l,m,n)) provisos (Add#(m,k,n), Add#(1,q,l));
  
  Reg#(ListN#(n,ListN#(l, Bit1))) state();
  mkRegU the_state(state); 

  Reg#(Bool) busy();
  mkReg#(False) the_busy(busy);

  // only process when the data is valid and when
  // the computation is not done
  rule wallaceStep (busy && !all(done,state));
    action
      ListN#(n,List#(Bit1)) x = map(toList,state);
      state <= map(padListToListN,statefulWallaceStep(x));
    endaction
  endrule: wallaceStep    

  method request();
    return (interface Put;
	      method put(inlistn) if (busy == False()); 
                  return(action 
                            state <= transpose(map(compose(padToNBits,unpack),inlistn));
                            busy  <= True();
                         endaction);
	      endmethod: put
	    endinterface: Put);
  endmethod: request

  method response(); return (interface Get;
                               method get() if ((busy == True()) && 
                                                (all(done,state)));
                                 actionvalue 
                                   busy <= False();
                                   return(pack(map(compose(head0,toList),state)));
                                 endactionvalue 
                               endmethod: get
                             endinterface: Get);
  endmethod: response

endmodule: mkStatefulWallace3

endpackage
