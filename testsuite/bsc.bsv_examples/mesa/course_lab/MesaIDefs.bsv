package MesaIDefs;

// The interface definitions for Mesa (greatly simplified for this
// transactional model.

// Required library packages:
import GetPut::*;
import ClientServer::*;
import RAM::*;

// Other Mesa packages:
import MesaDefs::*;


//
// For the VFF
//

// Input to the Vff, from the Spi/outside
typedef EthPacket IVffIn;

interface IVff;
    method Get#(IVffMifNotify) notify; // connected to mif.notify
    // method Server#(IVffMifRequest, IVffMifResponse) mif;
    method Server#(IVffDmRequest, IVffDmResponse) dm;
    method Put#(IVffIn) dta_in; // connected to Mesa input (via spir)
endinterface

//
// For the MIF
//

interface IMif;
    method Get#(Ftag) dm;
    method Put#(IVffMifNotify) notify; // connected to vff.notify
    // method Client#(IVffMifRequest, IVffMifResponse) vff;
    method Client#(Tuple2#(LuRequest,LuTag), Tuple2#(LuResponse, LuTag)) lpm;
endinterface

// When a packet arrives at the Vff, it notifies the Mif
//   In HW, it sends the port, base mem addr, pkt length, and status.
//   Here, we just send the Vff base mem addr and include the IP address
//   (which typically the Mif writes back and askes for).
typedef struct {
    VffBaseAddr vff_addr;
    VffPacketLength vff_pkt_len;
    IPAddr ip_dst_addr;
} IVffMifNotify deriving(Eq, Bits);

//  The following interfaces are not needed in this model:

//// The Mif requests a chunk of data from the Vff
////   In HW, it sends an addr and an offset and a Mif tag
////   Here we just request the IP address, and no tag needed
// typedef VffBaseAddr IVffMifRequest;

//// The Vff responds with the data
////   In HW, it sends the next chunk along with the tag
////   Here we get the IP address, and no tag
// typedef IPAddr IVffMifResponse;

//
// For the DM
//

interface IDm;
    method Put#(Ftag) mif;
    method Client#(IVffDmRequest, IVffDmResponse) vff;
    method Get#(IDmOut) dta_out; // connected to Mesa output (via spit)
endinterface

// The Dm requests a chunk of data from the Vff
//   In HW, it sends a port and an addr and a Dm tag
//   Here we just request a whole packet, so no length or tag needed
typedef VffBaseAddr IVffDmRequest;

// The Vff responds with the data
//   In HW, it sends the next chunk along with a port and a tag
//   Here we get the whole packet, and no tag
typedef EthPacket IVffDmResponse;

// Output of the Dm, to the Spi/outside
typedef RhPacket IDmOut;

//
// For the LPM
//

interface ILpm;
    method Server#(Tuple2#(LuRequest,LuTag), Tuple2#(LuResponse, LuTag)) mif;
    method RAMclient#(SramAddr, SramData) ram;
endinterface

endpackage: MesaIDefs
