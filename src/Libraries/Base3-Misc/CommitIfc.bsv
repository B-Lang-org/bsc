import ClientServer::*;
import Clocks::*;
import Connectable::*;
import FIFO::*;
import FIFOF::*;
import GetPut::*;
import SpecialFIFOs::*;
import FIFOLevel::*;

// An accept/acknowledge protocol which models opposite ends of FIFO
// Allows combinational connections without the troublesome AND gate.
// No execution order is applied between dataout and ack or datain and accept
// That is, one can signal accept before data arrives

interface SendCommit#(type a);
   method a dataout;
   (*always_ready*)
   method Action ack;
endinterface

interface RecvCommit#(type a);
   (*always_ready*)
   method Action datain (a din);
   (*always_ready*)
   method Bool accept ;
endinterface

////////////////////////////////////////////////////////////////////////////////
///  DefaultValue for Interface -- inactive interface
////////////////////////////////////////////////////////////////////////////////
instance DefaultValue#(SendCommit#(a))
   provisos (DefaultValue#(a));
   function defaultValue =
   (interface SendCommit;
      method a dataout if (False); return defaultValue ; endmethod
      method Action ack = noAction;
    endinterface);
endinstance
module mkNullSendCommit (SendCommit#(a))
   provisos (DefaultValue#(a));
   return defaultValue;
endmodule

instance DefaultValue#(RecvCommit#(a));
   function defaultValue =
   (interface RecvCommit;
      method Action datain (a din) = noAction;
      method Bool accept = False;
    endinterface);
endinstance
module mkNullRecvCommit (RecvCommit#(a))
   provisos (DefaultValue#(a));
   return defaultValue;
endmodule


////////////////////////////////////////////////////////////////////////////////
///  Connecting interface
////////////////////////////////////////////////////////////////////////////////
instance Connectable#(SendCommit#(a), RecvCommit#(a));
   module mkConnection #(SendCommit#(a) e, RecvCommit#(a) i) (Empty);
      (*fire_when_enabled*)
      rule connectData ;
         i.datain (e.dataout);
      endrule
      (*fire_when_enabled*)
      rule connectCommitAck (i.accept);
         e.ack;
      endrule
   endmodule
endinstance

instance Connectable#(RecvCommit#(a), SendCommit#(a));
   module mkConnection #(RecvCommit#(a) i, SendCommit#(a) e) (Empty);
      (*hide*)
      let _x <- mkConnection(e,i);
   endmodule
endinstance


instance Connectable#(SendCommit#(a), FIFOF#(a))
   provisos (Bits#(a,sa));
   module mkConnection #(SendCommit#(a) sc, FIFOF#(a) f) (Empty);
      RecvCommit#(a) rc <- mkRecvCommit(f);
      let conn <- mkConnection(sc,rc);
   endmodule
endinstance
instance Connectable#(FIFOF#(a), SendCommit#(a))
   provisos (Bits#(a,sa));
   module mkConnection #(FIFOF#(a) f, SendCommit#(a) sc) (Empty);
      (*hide*)
      let _x <- mkConnection(sc,f);
   endmodule
endinstance

instance Connectable#(RecvCommit#(a), FIFOF#(a))
   provisos (Bits#(a,sa));
   module mkConnection #(RecvCommit#(a) rc, FIFOF#(a) f) (Empty);
      SendCommit#(a) sc <- mkSendCommit(f);
      let conn <- mkConnection(rc,sc);
   endmodule
endinstance
instance Connectable#(FIFOF#(a), RecvCommit#(a))
   provisos (Bits#(a,sa));
   module mkConnection #(FIFOF#(a) f, RecvCommit#(a) rc) (Empty);
      (*hide*)
      let _x <- mkConnection(rc,f);
   endmodule
endinstance

instance Connectable#(SendCommit#(a), SyncFIFOIfc#(a))
   provisos (Bits#(a,sa));
   module mkConnection #(SendCommit#(a) sc, SyncFIFOIfc#(a) f) (Empty);
      RecvCommit#(a) rc <- mkRecvCommit(f);
      let conn <- mkConnection(sc,rc);
   endmodule
endinstance
instance Connectable#(SyncFIFOIfc#(a), SendCommit#(a))
   provisos (Bits#(a,sa));
   module mkConnection #(SyncFIFOIfc#(a) f, SendCommit#(a) sc) (Empty);
      (*hide*)
      let _x <- mkConnection(sc,f);
   endmodule
endinstance

instance Connectable#(RecvCommit#(a), SyncFIFOIfc#(a))
   provisos (Bits#(a,sa));
   module mkConnection #(RecvCommit#(a) rc, SyncFIFOIfc#(a) f) (Empty);
      SendCommit#(a) sc <- mkSendCommit(f);
      let conn <- mkConnection(rc,sc);
   endmodule
endinstance
instance Connectable#(SyncFIFOIfc#(a), RecvCommit#(a))
   provisos (Bits#(a,sa));
   module mkConnection #(SyncFIFOIfc#(a) f, RecvCommit#(a) rc) (Empty);
      (*hide*)
      let _x <- mkConnection(rc,f);
   endmodule
endinstance



////////////////////////////////////////////////////////////////////////////////
/// Typeclass for converting to these interfaces
/// These must use a module since rule and wires are reqwuired
////////////////////////////////////////////////////////////////////////////////
typeclass ToSendCommit#(type a , type b)
   dependencies (a determines b);
   module mkSendCommit#(a x) (SendCommit#(b));
endtypeclass

typeclass ToRecvCommit#(type a , type b)
   dependencies (a determines b);
   module mkRecvCommit#(a x) (RecvCommit#(b));
endtypeclass

/////////////////////////////////////////////////////
// Converting from for FIFO/ FIFOF
/////////////////////////////////////////////////////
instance ToSendCommit#(FIFO#(a), a);
   module mkSendCommit #(FIFO#(a) f) (SendCommit#(a));
      PulseWire doAck <- mkPulseWire;
      (*fire_when_enabled*)
      rule doDeq (doAck);
         f.deq;
      endrule
      method a dataout;
        return f.first;
      endmethod
      method Action ack = doAck.send;
   endmodule
endinstance
// ToRecvCommit#(FIFO#(a),a) is not possible  need to have notFull signal

instance ToSendCommit#(FIFOF#(a), a);
   // Assumes fifo has proper implicit conditions
   module mkSendCommit #(FIFOF#(a) f) (SendCommit#(a));
      PulseWire doAck <- mkPulseWire;
      (*fire_when_enabled*)
      rule doDeq (doAck /*&& f.notEmpty*/);
         f.deq;
      endrule
      method a dataout /*if (f.notEmpty)*/;
        return f.first;
      endmethod
      method Action ack = doAck.send;
   endmodule
endinstance

instance ToRecvCommit#(FIFOF#(a), a)
   provisos(Bits#(a,sa));
   // Assumes fifo has proper implicit conditions
   module mkRecvCommit #(FIFOF#(a) f) (RecvCommit#(a));
      RWire#(a) d <- mkRWire;
      (*fire_when_enabled*)
      rule doEnq (/*f.notFull &&& */ d.wget matches tagged Valid .data);
         f.enq(data);
      endrule
      method Action datain (a din);
         d.wset(din);
      endmethod
      method Bool accept = f.notFull;
   endmodule
endinstance

instance ToSendCommit#(SyncFIFOIfc#(a), a);
   // Assumes fifo has proper implicit conditions
   module mkSendCommit #(SyncFIFOIfc#(a) f) (SendCommit#(a));
      PulseWire doAck <- mkPulseWire;
      (*fire_when_enabled*)
      rule doDeq (doAck /*&& f.notEmpty*/);
         f.deq;
      endrule
      method a dataout /*if (f.notEmpty)*/;
        return f.first;
      endmethod
      method Action ack = doAck.send;
   endmodule
endinstance

instance ToRecvCommit#(SyncFIFOIfc#(a), a)
   provisos(Bits#(a,sa));
   // Assumes fifo has proper implicit conditions
   module mkRecvCommit #(SyncFIFOIfc#(a) f) (RecvCommit#(a));
      RWire#(a) d <- mkRWire;
      (*fire_when_enabled*)
      rule doEnq (/*f.notFull &&& */ d.wget matches tagged Valid .data);
         f.enq(data);
      endrule
      method Action datain (a din);
         d.wset(din);
      endmethod
      method Bool accept = f.notFull;
   endmodule
endinstance

instance ToSendCommit#(FIFOLevelIfc#(a,n), a);
   // Assumes fifo has proper implicit conditions
   module mkSendCommit #(FIFOLevelIfc#(a,n) f) (SendCommit#(a));
      PulseWire doAck <- mkPulseWire;
      (*fire_when_enabled*)
      rule doDeq (doAck /*&& f.notEmpty*/);
         f.deq;
      endrule
      method a dataout /*if (f.notEmpty)*/;
        return f.first;
      endmethod
      method Action ack = doAck.send;
   endmodule
endinstance

instance ToRecvCommit#(FIFOLevelIfc#(a,n), a)
   provisos(Bits#(a,sa));
   // Assumes fifo has proper implicit conditions
   module mkRecvCommit #(FIFOLevelIfc#(a,n) f) (RecvCommit#(a));
      RWire#(a) d <- mkRWire;
      (*fire_when_enabled*)
      rule doEnq (/*f.notFull &&& */ d.wget matches tagged Valid .data);
         f.enq(data);
      endrule
      method Action datain (a din);
         d.wset(din);
      endmethod
      method Bool accept = f.notFull;
   endmodule
endinstance

/////////////////////////////////////////////////////
// Converting from Get & Put Interfaces
// These introduce additional latency
/////////////////////////////////////////////////////
instance ToSendCommit#(Get#(a), a)
   provisos ( Bits#(a,sa));
   module mkSendCommit #(Get#(a) g) (SendCommit#(a));
      FIFOF#(a) convFIFOF <- mkBypassFIFOF;
      let connFIFOToGet <- mkConnection (g, toPut(convFIFOF));
      SendCommit#(a) fifofToSendCommit <- mkSendCommit(convFIFOF);
      return fifofToSendCommit;
   endmodule
endinstance

instance ToRecvCommit#(Put#(a), a)
   provisos(Bits#(a,sa));
   module mkRecvCommit #(Put#(a) p) (RecvCommit#(a));
      FIFOF#(a) convFIFOF <- mkBypassFIFOF;
      let connFIFOToPut <- mkConnection (p, toGet(convFIFOF));
      RecvCommit#(a) fifofToRecvCommit <- mkRecvCommit(convFIFOF);
      return fifofToRecvCommit;
   endmodule
endinstance


/////////////////////////////////////////////////////
// Converting from RWire Interfaces
// These reduce and or remove handshaking and may lose data.
/////////////////////////////////////////////////////
instance ToSendCommit#(RWire#(a), a) ;
   module mkSendCommit #(RWire#(a) r) (SendCommit#(a));
      // No action confuses clock crossing code.  Use this work-around.
      PulseWire unused <- mkPulseWire;
      method a dataout if (r.wget matches tagged Valid .d);
         return d;
      endmethod
      method Action ack = unused.send;
   endmodule
endinstance

instance ToRecvCommit#(RWire#(a), a) ;
   module mkRecvCommit #(RWire#(a) r) (RecvCommit#(a));
      method Action datain (a din);
         r.wset(din);
      endmethod
      method Bool accept = True;
   endmodule
endinstance

////////////////////////////////////////////////////////////////////////////////
///  Connecting to Get and Put Interfaces
//     These add fifos, but maintain loopless behavior
////////////////////////////////////////////////////////////////////////////////
instance Connectable#(SendCommit#(a), Put#(a))
   provisos (ToRecvCommit#(Put#(a),a));
   module mkConnection#(SendCommit#(a) sc, Put#(a) p) (Empty);
      RecvCommit#(a) rc <- mkRecvCommit(p);
      let connRCToSC <- mkConnection(rc, sc);
   endmodule
endinstance
instance Connectable#(Put#(a), SendCommit#(a))
   provisos (ToRecvCommit#(Put#(a),a));
   module mkConnection#(Put#(a) p, SendCommit#(a) sc) (Empty);
      (*hide*) let _i <- mkConnection(sc,p);
   endmodule
endinstance

instance Connectable#(RecvCommit#(a), Get#(a))
   provisos (ToSendCommit#(Get#(a),a));
   module mkConnection#(RecvCommit#(a) rc, Get#(a) g) (Empty);
      SendCommit#(a) sc <- mkSendCommit(g);
      let connSCToRC <- mkConnection(rc, sc);
   endmodule
endinstance
instance Connectable#(Get#(a), RecvCommit#(a))
   provisos (ToSendCommit#(Get#(a),a));
   module mkConnection#(Get#(a) g, RecvCommit#(a) rc) (Empty);
      (*hide*) let _i <- mkConnection(rc,g);
   endmodule
endinstance



////////////////////////////////////////////////////////////////////////////////
///  Clients and Servers variation
////////////////////////////////////////////////////////////////////////////////
interface ClientCommit#(type req, type resp);
   interface SendCommit#(req) request;
   interface RecvCommit#(resp) response;
endinterface

interface ServerCommit#(type req, type resp);
   interface RecvCommit#(req) request;
   interface SendCommit#(resp) response;
endinterface

module mkClientFromClientCommit #(ClientCommit#(req, resp) c) (Client#(req,resp))
   provisos ( Bits#(resp,_x), Bits#(req,_y));

   // Keep the reqFF at 2 deep to avoid long paths from FIFO's enq signal
   // to the accept method.
   FIFOF#(req) reqFF   <- mkFIFOF;
   // Use a 1 deep fifo here. long path is to Put interface
   FIFOF#(resp) respFF <- mkLFIFOF;
   let connRequest  <- mkConnection(reqFF, c.request);
   let connResponse <- mkConnection(respFF, c.response);
   interface Get request = toGet(reqFF);
   interface Put response = toPut(respFF);
endmodule


////////////////////////////////////////////////////////////////////////////////
///  Connecting ClientCommits and ServerCommits to Other Client Servers
////////////////////////////////////////////////////////////////////////////////
instance Connectable#(ClientCommit#(req,resp), ServerCommit#(req,resp));
   module mkConnection#(ClientCommit#(req,resp) c, ServerCommit#(req,resp) s)(Empty);
      let connBusCS_Request <- mkConnection(c.request, s.request);
      let connBusCS_Response <- mkConnection(c.response, s.response);
   endmodule
endinstance
instance Connectable#( ServerCommit#(req,resp), ClientCommit#(req,resp));
   module mkConnection#(ServerCommit#(req,resp) s, ClientCommit#(req,resp) c)(Empty);
      (*hide*) let _c <- mkConnection(c,s);
   endmodule
endinstance


instance Connectable #(ClientCommit#(req,resp), Server#(req,resp))
   provisos ( Bits#(resp,_x), Bits#(req,_y));
   module mkConnection #(ClientCommit#(req,resp) bc, Server#(req,resp) s)(Empty);
      let connBClient_Server_Request <- mkConnection(bc.request, s.request);
      let connBClient_Server_Reponse <- mkConnection(bc.response, s.response);
   endmodule
endinstance
instance Connectable #( Server#(req,resp), ClientCommit#(req,resp))
   provisos ( Bits#(resp,_x), Bits#(req,_y));
   module mkConnection #( Server#(req,resp) s, ClientCommit#(req,resp) bc)(Empty);
      (*hide*) let _c <- mkConnection(bc,s);
   endmodule
endinstance

instance Connectable #(ServerCommit#(req,resp), Client#(req,resp))
   provisos ( Bits#(resp,_x), Bits#(req,_y));
   module mkConnection #(ServerCommit#(req,resp) bs, Client#(req,resp) c)(Empty);
      let connBServer_Client_Request <- mkConnection(bs.request, c.request);
      let connBServer_Client_Reponse <- mkConnection(bs.response, c.response);
   endmodule
endinstance
instance Connectable #( Client#(req,resp), ServerCommit#(req,resp))
   provisos ( Bits#(resp,_x), Bits#(req,_y));
   module mkConnection #( Client#(req,resp) c, ServerCommit#(req,resp) bs)(Empty);
      (*hide*) let _c <- mkConnection(bs,c);
   endmodule
endinstance

////////////////////////////////////////////////////////////////////////////////
///  Converting SendCommit and RecvCommit to Get and Put
///  These function introduce a combinational loop between the commit ifc methods
////////////////////////////////////////////////////////////////////////////////
instance ToGet#(SendCommit#(a), a);
   function Get#(a) toGet(SendCommit#(a) sc);
      return
      (interface Get
          method ActionValue#(a) get ();
             sc.ack;
             return sc.dataout;
          endmethod
       endinterface);
   endfunction
endinstance

instance ToPut#(RecvCommit#(a), a);
   function Put#(a) toPut (RecvCommit#(a) rc);
      return
      (interface Put;
          method Action put(a din) if (rc.accept);
             rc.datain(din);
          endmethod
      endinterface);
   endfunction
endinstance
