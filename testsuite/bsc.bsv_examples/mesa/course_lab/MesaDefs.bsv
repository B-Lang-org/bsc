package MesaDefs;

// The various global definitions for the Mesa design (except for the
// interface definitions, which are in MesaIDefs).

// The RAM interface type definition is imported from the library:
import RAM::*;

// The SRAM's parameters' types:
typedef Bit#(21) SramAddr;
typedef Bit#(32) SramData;
typedef Bit#(1)  SramWrite;
typedef Bit#(8)  SriTag;

typedef RAM#(SramAddr, SramData) Dram;

// IP Lookup types
typedef Bit#(32) LuRequest;
typedef Bit#(32) LuResponse;

typedef Bit#(5) LuTag;

// IPv4 Packet structure and types (greatly simplified for this model): 
typedef Bit#(32) IPAddr;
typedef Bit#(16) PktByteSize;
typedef Bit#(16) IPLength;

typedef struct {
    IPAddr  dst_addr;
    IPLength  length;
    Bit#(32)  marker;
} IPPacket deriving(Eq, Bits);

// A general IP packet (the extra generality commented out for this model): 
typedef union tagged {
    IPPacket IPv4;
    // IPv6Packet IPv6; ?
    // MCPacket MC; ?
} L3Pkt deriving (Eq, Bits);

// Ethernet Packets (the level-2 components commented out for this model):
typedef Bit#(16) EthLength;

typedef struct {
    // dst addr
    // src addr
    EthLength length;
    L3Pkt l3pkt;
    // padding ?
} EthPacket deriving(Eq, Bits);

// A function to calculate the length of an ethernet packet based on the
// length of the IP packet it contains:
function EthLength getEthLength(EthPacket epkt);
    let l3len  = epkt.length;  // getL3Length epkt.l3pkt;
    let hdrlen = 14 + 4;  // 14 bytes before data, 4 crc after data

    // header has a padding field of 0-46 bytes since min size is 64 bytes
    return (max(64, l3len + hdrlen));
endfunction

// Mesa Output
// The Mesa attaches a routing header to the ethernet packet, so that the
// switching fabric can route it to the correct output node.
typedef struct {
    RouteHeader  route_hdr;
    EthPacket pkt;
} RhPacket deriving(Eq, Bits);

// The Routing Header's structure:
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

// Types for internal communication within Mesa:
typedef Bit#(14) VffPacketLength;
typedef Bit#(10) VffAddr;
typedef VffAddr  VffBaseAddr;

typedef struct {
    VffPacketLength length;
    VffBaseAddr addr;
    RouteHeader route_header;
} Ftag deriving(Eq, Bits);


endpackage: MesaDefs
