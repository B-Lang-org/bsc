
import FIFO :: *;
import GetPut :: *;
import ClientServer :: *;
import Connectable :: * ;

typedef Tuple2#(Bit#(8), Bit#(8))   REQ;
typedef Bit#(16)                    RSP;

(* synthesize *)
module sysTestToGPClientServer ();

   Server#(REQ, RSP) s <- mkServer;
   Client#(REQ, RSP) c <- mkClient;

   mkConnection (s, c);

   Reg#(Bit#(10)) ticks <- mkReg(0);

   rule cnt ;
      ticks <= ticks + 1;
      if (ticks > 50) $finish(0);
   endrule

endmodule

module mkServer(Server#(REQ,RSP));
   FIFO#(REQ)  f_req <- mkFIFO;
   FIFO#(RSP)  f_rsp <- mkFIFO;

   Server#(REQ, RSP) sf = toGPServer(f_req, f_rsp);

   rule do_server;
      match { .v1, .v2 } = f_req.first;
      f_req.deq;
      RSP rs = extend(v1) * extend(v2);
      f_rsp.enq(rs);
   endrule

   return sf;
endmodule

module mkClient(Client#(REQ,RSP));
   FIFO#(REQ)  f_req <- mkFIFO;
   FIFO#(RSP)  f_rsp <- mkFIFO;

   Client#(REQ, RSP) cf = toGPClient(f_req, f_rsp);

   Reg#(Bit#(8)) r_v1 <- mkReg(0);
   Reg#(Bit#(8)) r_v2 <- mkReg(1);

   rule do_req;
      REQ rq = tuple2(r_v1, r_v2);
      f_req.enq(rq);
      let next_v1 = r_v1 + 1;
      let next_v2 = r_v2 * 2;
      r_v1 <= next_v1;
      r_v2 <= ((next_v2 == 0) ? 1 : next_v2);
   endrule

   rule do_rsp;
      RSP rs = f_rsp.first;
      f_rsp.deq;
      $display("Client received response: %d", rs);
   endrule

   return cf;
endmodule
