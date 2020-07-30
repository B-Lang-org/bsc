// Filename        : Mesa.bsv ~/bsc/examples/mesa/spiless-tx-bsv/test2/
// Description     : 
import MesaDefs::*;
import MesaIDefs::*;

import Mesa_Vff::*;
import Mesa_Dm::*;
import MesaTxLpm::*;
import Mesa_Mif::*;

import ClientServer::*;
import Connectable::*;
import GetPut::*;
import RAM::*;


interface IMesa;
   method Put#(EthPacket) dta_in;
   method Get#(RhPacket) dta_out;
   method RAMclient#(SramAddr,SramData) dram;
endinterface


(* synthesize *)
module mkMesa(IMesa);
    IVff vff();
    mkMesa_Vff the_vff(vff);

    IDm dm();
    mkMesa_Dm the_dm(dm);

    //dm.vff <-> vff.dm
    mkConnection(dm.vff, vff.dm);

   ILpm lpm();
   mkMesaTxLpm the_lpm(lpm);

    IMif mif();
    mkMesa_Mif the_mif(mif);

    // mif.notify <-> vff.notify
    // mif.dm <-> dm.mif
    // mif.lpm <-> lpm.mif
    mkConnection(mif.notify, vff.notify);
    mkConnection(mif.dm, dm.mif);
    mkConnection(mif.lpm, lpm.mif);

    // This connection not used in this level of modeling
    // mif.vff <-> vff.mif
    // mkConnection(mif.vff, vff.mif);

    return (interface IMesa;
	       method dta_in();  return vff.dta_in;  endmethod
	       method dta_out(); return dm.dta_out;  endmethod
	       method dram();    return lpm.ram;     endmethod
	    endinterface);
endmodule: mkMesa


