import GetPut::*;
import ClientServer::*;
import FIFO::*;
import Connectable::*;
import Vector::*;
import Test::*;

// Hierarchy test for virtual class
typedef UInt#(14) I;
typedef UInt#(14) O;
typedef 3   SIZE;


(*synthesize, options ="-elab"*)
module sysHierTest2 #(Inout#(Bar) i) (Empty);
   Vector#(SIZE,Server#(I,O))  m$$$s <- replicateM(mkHierTest2);
   let x1 <- mkConnection(m$$$s[0].request, m$$$s[1].response);
   let x2 <- mkConnection(m$$$s[1].request, m$$$s[2].response);
   
   // 
   Foo#(Bit#(4)) mb <- mkBVI(17, i);
   (*hide*)
   Foo#(Bit#(4)) mb_hidden <- mkBVI(17, i);
endmodule

(*synthesize, options ="-elab"*)
module mkHierTest2 (Server#(I,O) );
   FIFO#(I) inf <- mkFIFO;
   FIFO#(O) outf <- mkFIFO;

   ClientServer#(I,O) cs <- mkRequestResponseBuffer;
   let c1 <- mkConnection(tpl_2(cs), fifosToClient(inf, outf));

   Client#(I,O) sss = tpl_1(cs);

   RWire#(I) rw$fff <- mkRWire;
   PulseWire pw <- mkPulseWire;
   Wire#(I) ww <- mkDWire(17);

   rule tpro$cess;
      I req <- sss.request.get;
      sss.response.put(truncate(req));
      rw$fff.wset(req);
      pw.send;
      ww <= req;
   endrule

   return fifosToServer(inf, outf);
endmodule
