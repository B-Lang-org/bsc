package MesaDefs;

import RAM::*;

//
// SRAM
//

typedef Bit#(21) SramAddr;
typedef Bit#(32) SramData;
typedef Bit#(1)  SramWrite;
typedef Bit#(8)  SriTag;

typedef RAM#(SramAddr, SramData) Dram;

//
// IP Lookup
//

typedef Bit#(32) LuRequest;
typedef Bit#(32) LuResponse;

typedef Bit#(5) LuTag;

//
// IP v4 Packets
//

typedef Bit#(32) IPAddr;
typedef Bit#(16) PktByteSize;

typedef struct {
		IPAddr  dst_addr;
		IPLength  length;
		Bit#(32)  marker;
} IPPacket deriving(Eq, Bits);

typedef Bit#(16) IPLength;

typedef union tagged {
    IPPacket IPv4;
    // IPv6Packet IPv6; ?
    // MCPacket MC; ?
} L3Pkt deriving (Eq, Bits);


//
// Ethernet Packets
//

typedef struct {
    // dst addr
    // src addr
    EthLength length;
    L3Pkt l3pkt;
    // padding ?
} EthPacket deriving(Eq, Bits);

typedef Bit#(16) EthLength;

function EthLength getEthLength(EthPacket epkt);
    let l3len  = epkt.length;  // getL3Length epkt.l3pkt;
    let hdrlen = 14 + 4;  // 14 bytes before data, 4 crc after data

    // header has a padding field of 0-46 bytes since min size is 64 bytes
    return (max(64, l3len + hdrlen));
endfunction


//
// Mesa Output
//

typedef struct {
    RouteHeader  route_hdr;
    EthPacket pkt;
} RhPacket deriving(Eq, Bits);


//
// Routing Header
//

typedef Bit#(6)  RhNode;
typedef Bit#(5)  RhPort;
typedef Bit#(3)  RhCoS;
typedef Bit#(2)  RhDp;
typedef Bit#(1)  RhEcn;
typedef Bit#(1)  RhTest;
typedef Bit#(14) RhLength;
typedef Bit#(4)  RhType;
typedef Bit#(20) RhCtlWord;

typedef struct {
    RhNode    node;
    RhPort    port;
    RhCoS     cos;
    RhDp      dp;
    RhEcn     ecn;
    RhTest    test;
    RhLength  length;
    RhType    pkttype;
    RhCtlWord ctlWord;
    Bit#(8)   reserved;
} RouteHeader deriving(Eq, Bits);


//
// Internal communication
//

typedef Bit#(14) VffPacketLength;
typedef Bit#(10) VffAddr;
typedef VffAddr  VffBaseAddr;

typedef struct {
    VffPacketLength length;
    VffBaseAddr addr;
    RouteHeader route_header;
} Ftag deriving(Eq, Bits);


endpackage: MesaDefs
