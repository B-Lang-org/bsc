import FIFO::*;

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

module  mk3ROMports#(ROM#(lat) rom) (ROM3#(lat1)) provisos (Add#(lat,1,lat1));
    FIFO#(Tag) tags();
    mkSizedFIFO#(valueOf(lat)) the_tags(tags);

    module mkPort#(Tag i) (ROM#(lat1));
	FIFO#(Dta) out();
	mkSizedFIFO#(valueOf(lat)) the_out(out);

        rule deq_rule (tags.first == i);
	    action
	      tags.deq();
	      rom.ack();
	      out.enq(rom.result());
            endaction
        endrule

        method read(Adr a);
	    action
	        rom.read(a);
	        tags.enq(i);
	    endaction
	endmethod
	method result(); return(out.first()); endmethod
	method ack(); return(out.deq()); endmethod
    endmodule

    ROM#(lat1) port0_ifc();
    mkPort#(0) the_port0(port0_ifc);

    ROM#(lat1) port1_ifc();
    mkPort#(1) the_port1(port1_ifc);

    ROM#(lat1) port2_ifc();
    mkPort#(2) the_port2(port2_ifc);

    interface port0 = port0_ifc;
    interface port1 = port1_ifc;
    interface port2 = port2_ifc;

endmodule
