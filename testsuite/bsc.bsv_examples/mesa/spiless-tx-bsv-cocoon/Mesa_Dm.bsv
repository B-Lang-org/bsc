import FIFO::*;
import GetPut::*;
import ClientServer::*;
import ClientServerLib::*;

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
	let vff_addr = ftag.addr;
	let pkt_len = ftag.length;
	let rheader = ftag.route_header;

	fifoRouteHeader.enq(rheader);
	vff_req_fifo.enq(vff_addr);  // pkt_len not needed?
	mif_in_fifo.deq();
    endrule

    rule handle_vff_res (True);
        let pkt = vff_res_fifo.first();
	let rheader = fifoRouteHeader.first();
	let rhpkt = RhPacket { route_hdr: rheader, pkt: pkt };

	spi_out_fifo.enq(rhpkt);
	vff_res_fifo.deq();
	fifoRouteHeader.deq();
    endrule


    method mif();
       return fifoToPut(mif_in_fifo);
    endmethod

    method vff();
       return mkClientFromFIFOs(vff_req_fifo, vff_res_fifo);
    endmethod

    method dta_out();
       return fifoToGet(spi_out_fifo);
    endmethod

endmodule: mkMesa_Dm

