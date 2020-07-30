package WallaceTest;

import GetPut::*;

import ClientServer::*;

import ListN::*;

import WallaceServer::*;

import FIFOF::*;

import Connectable::*;

import WallaceServer::*;

import CombWallace::*;

import StatefulWallace::*;

// utility function used to check the result of a Wallace addition
function Bit#(n) sumList(ListN#(l, Bit#(m)) theInput) provisos (Add#(m,q,n)); 
      ListN#(l, Bit#(n)) extended; 
      extended = map(zeroExtend,theInput);
      return (foldr(add,0,extended));
endfunction: sumList 

module mkWallaceTestClient(WallaceClient#(l,m,n)) provisos (Mul#(l,m,k),
                                                            Add#(m,q,n));
 
   // iterate through all bit patterns to get all possible test inputs
   Reg#(Bit#(k)) r(); 
   mkReg#(0) the_r(r);

   // keep track of in-flight requests for validation
   FIFOF#(ListN#(l, Bit#(m))) requests();
   mkSizedFIFOF#(valueOf(n)) the_requests(requests);

   // need to remember when to stop yielding values
   Reg#(Bool) doneget();
   mkReg#(False) the_doneget(doneget);

   rule finish
     ( doneget && !(requests.notEmpty)); $finish(0);
   endrule: finish

   method request();
     return (interface Get;
               method get() if (!doneget);
                 actionvalue
                   ListN#(l, Bit#(m)) val = unpack(r);
                   r <= r + 1;
                   if ((r + 1) == 0) doneget <= True;
                   requests.enq(val); 
                   return(val);
                 endactionvalue
               endmethod: get
             endinterface: Get);
   endmethod: request 

   method response();
     return (interface Put;
               method put(result);
                 action
                   ListN#(l, Bit#(m)) theInput;
                   theInput = requests.first();
                   requests.deq();
                   Bit#(n) expected = sumList(theInput);
                   if(result == expected) 
                       $display("Pass: pattern: %b result: %b", theInput, result);
                   else
                       $display("Fail: pattern: %b expected: %b result: %b", theInput, expected, result);
                 endaction
               endmethod: put
             endinterface: Put);
   endmethod: response
       
endmodule: mkWallaceTestClient

// many different wallace adders synthesized with
// associated testbenches

(* synthesize *)
module sysCombServer(WallaceServer#(4,3,5));
   WallaceServer#(4,3,5) server();
   mkCombWallace my_server(server);
   return(server);
endmodule: sysCombServer

(* synthesize *)
module sysStatefulServer1(WallaceServer#(4,3,5));
   WallaceServer#(4,3,5) server();
   mkStatefulWallace1 my_server(server);
   return(server);
endmodule: sysStatefulServer1
   
(* synthesize *)
module sysStatefulServer2(WallaceServer#(4,3,5));
   WallaceServer#(4,3,5) server();
   mkStatefulWallace2 my_server(server);
   return(server);
endmodule: sysStatefulServer2
   
(* synthesize *)
module sysStatefulServer3(WallaceServer#(4,3,5));
   WallaceServer#(4,3,5) server();
   mkStatefulWallace3 my_server(server);
   return(server);
endmodule: sysStatefulServer3

(* synthesize *)
module testCombServer(Empty);
   WallaceServer#(4,3,5) server();
  sysCombServer the_server(server);

  WallaceClient#(4,3,5) client();
  mkWallaceTestClient the_client(client);

  mkConnection(client,server);

endmodule: testCombServer

(* synthesize *)
module testStatefulServer1(Empty);
  WallaceServer#(4,3,5) server();
  sysStatefulServer1 the_server(server);

  WallaceClient#(4,3,5) client();
  mkWallaceTestClient the_client(client);

  mkConnection(client, server);

endmodule: testStatefulServer1

(* synthesize *)
module testStatefulServer2(Empty);
  WallaceServer#(4,3,5) server();
  sysStatefulServer2 the_server(server);

  WallaceClient#(4,3,5) client();
  mkWallaceTestClient the_client(client);

  mkConnection(client, server);

endmodule: testStatefulServer2

(* synthesize *)
module testStatefulServer3(Empty);
  WallaceServer#(4,3,5) server();
  sysStatefulServer3 the_server(server);

  WallaceClient#(4,3,5) client();
  mkWallaceTestClient the_client(client);

  mkConnection(client, server);

endmodule: testStatefulServer3

endpackage
