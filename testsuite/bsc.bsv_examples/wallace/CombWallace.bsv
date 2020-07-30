package CombWallace;

import WallaceLib::*;

import WallaceServer::*;

import GetPut::*;

import ClientServer::*;

import ListN::*;

// A combinational Wallace adder
// Most of the work is done by library procedeures
// This is a shell implementing the Server interface
// so the combinational adder can be connected to the testbench
module mkCombWallace(WallaceServer#(l,m,n)) provisos (Add#(m,k,n));
  
  Reg#(Bit#(n)) result();
  mkReg#(0) the_result(result);

  Reg#(Bool) valid();
  mkReg#(False()) the_valid(valid);

  method request(); return (interface Put;
	                      method put(inlistn); 
                                action
                                  List#(Bit#(m)) inlist = toList(inlistn); 
                                  result <= wallaceAdd(inlist);
                                  valid  <= True();
                                endaction
	                      endmethod: put
	                    endinterface: Put);
  endmethod: request

  method response(); return (interface Get;
                               method get() if (valid == True());
                                 actionvalue 
                                   valid <= False();
                                   return(result);
                                 endactionvalue 
                               endmethod: get
                             endinterface: Get);
  endmethod: response

endmodule: mkCombWallace

endpackage
