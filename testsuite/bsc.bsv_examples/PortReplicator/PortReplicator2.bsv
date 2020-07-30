import FIFO::*;
import Counter::*;

import AsyncROM::*;

typedef Bit#(32) Adr;
typedef Bit#(32) Dta;

typedef Bit#(2) Tag;

typedef AsyncROM#(lat,Adr,Dta) ROM#(type lat);

interface ROM3#(type lat);
    interface ROM#(lat) port0;
    interface ROM#(lat) port1;
    interface ROM#(lat) port2;
endinterface


module  mk3ROMports#(ROM#(lat) rom) (ROM3#(lat1))
    provisos (Add#(lat,1,lat1), Log#(lat1,loglat1));

    FIFO#(Tag) tags <- mkSizedFIFO(valueOf(lat));

    module mkPort#(Tag i) (ROM#(lat1));
	FIFO#(Dta) out();
	mkSizedFIFO#(valueOf(lat)) the_out(out);

	Counter#(loglat1) cnt();
	mkCounter#(fromInteger(valueOf(lat))) the_cnt(cnt);

        rule deq_rule (tags.first == i);	 
	      out.enq(rom.result());
	      tags.deq();
	      rom.ack();
        endrule

        method read(Adr a) if (cnt.value > 0);
	    action
	        rom.read(a);
	        tags.enq(i);
		cnt.down();
	    endaction
	endmethod
	method result(); return(out.first()); endmethod
	method ack();
	    action
	        out.deq();
		cnt.up();
	    endaction
	endmethod
    endmodule

    ROM#(lat1) port0_ifc <- mkPort(0);
    ROM#(lat1) port1_ifc <- mkPort(1);
    ROM#(lat1) port2_ifc <- mkPort(2);

    interface port0 = port0_ifc;
    interface port1 = port1_ifc;
    interface port2 = port2_ifc;

endmodule
