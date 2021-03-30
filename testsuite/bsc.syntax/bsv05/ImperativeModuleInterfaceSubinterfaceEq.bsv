import GetPut::*;
import ClientServer::*;

interface FooIfc;
  interface Server#(Bool, Bool) server;
  method Bool isBogus();
endinterface

Put#(Bool) reqIfc =
  interface Put
    method put(x); action endaction endmethod
  endinterface;

module mkFoo(FooIfc);
  Reg#(Bool) ifc;

  interface Server server;
    interface request = reqIfc;
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
