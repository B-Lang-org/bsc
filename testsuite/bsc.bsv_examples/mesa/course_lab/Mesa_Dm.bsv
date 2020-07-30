// The "data mover" submodule.  In the real hardware this reassembles a packet
// and ships it out to the SPI interface.  This transactional version is
// greatly simplified.

import FIFO::*;
import GetPut::*;
import ClientServerLib::*;
import ClientServer::*;

import MesaDefs::*;
import MesaIDefs::*;

(* synthesize *)
module mkMesa_Dm (IDm);

   // input FIFO from mif
   FIFO#(Ftag) mif_in_fifo();
   mkFIFO the_mif_in_fifo(mif_in_fifo);
   
   // output FIFO to Mesa output (via spit)
   FIFO#(IDmOut) spi_out_fifo();
   mkFIFO the_spi_out_fifo(spi_out_fifo);
   
   // In the hardware version, these next FIFOs would be handling the
   // retrieval of the packet body from the VFF memory.  Here it's just one
   // request and response.
   
   // VFF request FIFO
   FIFO#(IVffDmRequest) vff_req_fifo();
   mkFIFO the_vff_req_fifo(vff_req_fifo);
   
   // VFF result FIFO
   FIFO#(IVffDmResponse) vff_res_fifo();
   mkFIFO the_vff_res_fifo(vff_res_fifo);
   
   
   // FIFO of route headers waiting to go out, once VFF returns the packet
   FIFO#(RouteHeader) fifoRouteHeader();
   mkFIFO the_fifoRouteHeader(fifoRouteHeader);
   
   
   rule handle_mif (True);
      let ftag = mif_in_fifo.first();
      mif_in_fifo.deq();
      
      let vff_addr = ftag.addr;
      let pkt_len = ftag.length;
      let rheader = ftag.route_header;
      
      fifoRouteHeader.enq(rheader);
      vff_req_fifo.enq(vff_addr);  // pkt_len not needed?
   endrule
   
   rule handle_vff_res (True);
      let pkt = vff_res_fifo.first();
      vff_res_fifo.deq();
      
      let rheader = fifoRouteHeader.first();
      fifoRouteHeader.deq();
      
      let rhpkt = RhPacket { route_hdr: rheader, pkt: pkt };
      spi_out_fifo.enq(rhpkt);
   endrule
   
   interface mif = fifoToPut(mif_in_fifo);
   interface vff = mkClientFromFIFOs(vff_req_fifo, vff_res_fifo);
   interface dta_out = fifoToGet(spi_out_fifo);
   
endmodule: mkMesa_Dm

