import Connectable::*;
import BRAM::*;

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

typedef Server#(SRAM_Request_t#(addr_t, data_t), SRAM_Response_t#(data_t))
                                 IFC_SRAM_Server #(type addr_t, type data_t);

// the interface presented by the SRAM client (controller, uP, etc.):
//   the request is "got" and the response "set" by the connected SRAM

typedef Client#(SRAM_Request_t#(addr_t, data_t), SRAM_Response_t#(data_t))
                                 IFC_SRAM_Client #(type addr_t, type data_t);

// Define how to convert SRAM client to a BRAM client:

function BRAMRequest#(addr, data) sramReqToBram(SRAM_Request_t#(addr, data) r);
   let wr = False;
   let ad = ?;
   let dt = ?;
   case (r) matches
      tagged SRAM_Read { address: .a }: ad = a;
      tagged SRAM_Write { address: .a, data: .d }:
	 begin
	    ad = a;
	    dt = d;
	    wr = True;
	 end
   endcase
   return BRAMRequest {write : wr,
		       responseOnWrite : False,
		       address : ad,
		       datain :  dt
		       };
endfunction

function data sramRespToBram(SRAM_Response_t#(data) r) = r.data;

function BRAMClient#(addr, data) sramClientToBramClient(IFC_SRAM_Client#(addr, data) c) =
   (interface Client;
       interface Put response;
	  method Action put(x);
	     c.response.put(SRAM_Response_t {data: x});
	  endmethod
       endinterface
       interface Get request;
	  method get();
	     actionvalue
	        let r <- c.request.get();
		return sramReqToBram(r);
	     endactionvalue
	  endmethod
       endinterface
    endinterface);
