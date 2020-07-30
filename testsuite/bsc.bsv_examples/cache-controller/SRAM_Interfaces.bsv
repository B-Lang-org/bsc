import Connectable::*;

// the SRAM request type
// the physical layout is
//   +-+--...---+---...---+
//   |r|  data  | address |
//   +-+--...---+---...---+
// where r is the "read?" tag, or the active-low write-enable
typedef union tagged {
    struct {
        addr_t address;
    } SRAM_Read;
    struct {
        data_t data;
        addr_t address;
    } SRAM_Write;
} SRAM_Request_t #(type addr_t, type data_t) deriving(Eq, Bits);

// the SRAM response type
// the physical layout is
//   +--...---+
//   |  data  |
//   +--...---+
typedef struct {
    data_t data;
} SRAM_Response_t#(type data_t) deriving(Eq, Bits);

// the interface presented by the SRAM:
//   the request is "set" and the response "got" by the connected client
interface IFC_SRAM_Server #(type addr_t, type data_t);
    method Action set_request(SRAM_Request_t#(addr_t, data_t) req);
    method SRAM_Response_t#(data_t) get_response();
endinterface: IFC_SRAM_Server

// the interface presented by the SRAM client (controller, uP, etc.):
//   the request is "got" and the response "set" by the connected SRAM
interface IFC_SRAM_Client #(type addr_t, type data_t);
    method SRAM_Request_t#(addr_t, data_t) get_request();
    method Action set_response(SRAM_Response_t#(data_t) data);
endinterface: IFC_SRAM_Client

// define how to connect SRAM client and server
instance Connectable#(IFC_SRAM_Client#(addr_t, data_t),
                      IFC_SRAM_Server#(addr_t, data_t));
    module mkConnection#(IFC_SRAM_Client#(addr_t, data_t) client,
                         IFC_SRAM_Server#(addr_t, data_t) server)();
        (* fire_when_enabled *)
        rule pass_request;
            server.set_request(client.get_request);
        endrule
        (* fire_when_enabled *)
        rule pass_response;
            client.set_response(server.get_response);
        endrule
    endmodule
endinstance

// define how to connect SRAM server and client (reduced to case above)
instance Connectable#(IFC_SRAM_Server#(addr_t, data_t),
                      IFC_SRAM_Client#(addr_t, data_t));
    function mkConnection(x, y) = mkConnection(y,x);
endinstance

