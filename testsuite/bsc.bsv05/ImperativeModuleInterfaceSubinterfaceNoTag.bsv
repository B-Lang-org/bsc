import GetPut::*;
import ClientServer::*;

interface FooIfc;
  interface Server#(Bool, Bool) server;
  method Bool isBogus();
endinterface

module mkFoo(FooIfc);
  Reg#(Bool) ifc;

  interface server;
    interface Put request;
      method put(x);
        action
        endaction
      endmethod: put
    endinterface: request
    interface Get response;
      method get();
        actionvalue
          return False;
        endactionvalue
      endmethod: get
    endinterface: response
  endinterface: server
  method Bool isBogus();
    isBogus = True;
  endmethod
endmodule
