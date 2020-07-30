// "fake" implementation of an SRAM, as a register file, for testing

import SRAM_Interfaces::*;
import RegFile::*;

module mkSRAM #(addr_t depth)(IFC_SRAM_Server#(addr_t, data_t))
    provisos (Bits#(addr_t, addr_sz), Bits#(data_t, data_sz));
    
    data_t poison_data = unpack('1); // to return at init and on writes
    
    RegFile #(addr_t, data_t) mem <- mkRegFile(unpack(0), depth);
    Reg #(data_t) data_out <- mkReg(poison_data);

    method Action set_request(SRAM_Request_t#(addr_t, data_t) req);
        case (req) matches
            tagged SRAM_Write { data: .data_in, address: .addr_in }:
                begin
                    mem.upd(addr_in, data_in);
                    data_out <= poison_data;
//                    $display("INFO (fake sram): write @%h: %h", addr_in, data_in);
                end
            tagged SRAM_Read { address: .addr_in }:
                begin
                    data_out <= mem.sub(addr_in);
//                    $display("INFO (fake sram): read @%h: %h", addr_in, mem.sub(addr_in));  
                end
        endcase
    endmethod

    method SRAM_Response_t#(data_t) get_response();
        return (SRAM_Response_t { data: data_out });
    endmethod
endmodule: mkSRAM

