import GetPut::*;
import ClientServer::*;

interface CHANNEL;
  interface Client#(Bit#(64), Bit#(64)) client;
endinterface

module mkChannel (CHANNEL);

  interface Client client;
     Bool x = True;
  endinterface

endmodule

