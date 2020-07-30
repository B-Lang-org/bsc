// --------------------------------------------------------
//
//    This bluespec module contains a case statement which
//    causes an error report that seems equivalent to a core 
//    dump.
//
//    I put the error messages at the bottom of this file.
//    The error message does not give a line number.  When
//    many registers are defined the error report is 
//    huge. This error message is also at the bottom of this
//    file.
//
// ---------------------------------------------------------
//

typedef bit  [7:0] Addr_type;
typedef bit [31:0] Data_type;

interface Interface_reg #(type addr_type, type data_type);
   
   // define write template
   method Action write(
      addr_type addr, 
      data_type data_out
   );
   
   // define read template
   method data_type   read(addr_type addr);

   // AMBA MASTER METHODS
   
endinterface // interface_reg


(* synthesize *)
module dmac (Interface_reg #(Addr_type,Data_type));

   method Data_type read(Addr_type addr); 

      // ******** THIS CASE STATEMENT CAUSES THE ERROR ***************

      case (addr)
         default: read = 32'b0;
      endcase
   endmethod // read 


   method Action write (Addr_type addr, Data_type data_out);
      action
      endaction
   endmethod // write

endmodule // module_reg


// ===================================================================
// ===================================================================
// ===================================================================

// ERROR MESSAGE FOR THIS SMALL, SIMPLE CASE
//bsc -verilog case_bug.bsv
//
//Fail: BSC ERROR: findT _d1093
//[(addr, Prelude.Bit 8)]
//


// ERROR MESSAGE WHEN I HAD MANY REGISTERS DEFINED
//
//
//bsc -verilog case_bug.bsv
//
//Fail: BSC ERROR: findT _d2206
//[(addr, Prelude.Bit 8),
// (reg0, Prelude.Reg (Prelude.Bit 32)),
// (reg1, Prelude.Reg (Prelude.Bit 32)),
// (reg2, Prelude.Reg (Prelude.Bit 32)),
// (reg3, Prelude.Reg (Prelude.Bit 32)),
// (reg4, Prelude.Reg (Prelude.Bit 32)),
// (updown_cnt, Prelude.Reg (Prelude.Bit 32)),
// (write_strobe, Prelude.Reg (Prelude.Bit 16)),
// (count_up, Prelude.Reg (Prelude.Bit 1)),
// (count_down, Prelude.Reg (Prelude.Bit 1)),
// (transfer_size, Prelude.Reg (Prelude.Bit 32)),
// (transfer_cnt, Prelude.Reg (Prelude.Bit 32)),
// (src_burst_size, Prelude.Reg (Prelude.Bit 32)),
// (src_current_addr, Prelude.Reg (Prelude.Bit 32)),
// (src_step_size, Prelude.Reg (Prelude.Bit 32)),
// (src_stop_addr, Prelude.Reg (Prelude.Bit 32)),
// (src_min_addr, Prelude.Reg (Prelude.Bit 32)),
// (src_max_addr, Prelude.Reg (Prelude.Bit 32)),
// (src_configuration, Prelude.Reg (Prelude.Bit 32)),
// (dest_burst_size, Prelude.Reg (Prelude.Bit 32)),
// (dest_current_addr, Prelude.Reg (Prelude.Bit 32)),
// (dest_step_size, Prelude.Reg (Prelude.Bit 32)),
// (dest_stop_addr, Prelude.Reg (Prelude.Bit 32)),
// (dest_min_addr, Prelude.Reg (Prelude.Bit 32)),
// (dest_max_addr, Prelude.Reg (Prelude.Bit 32)),
// (dest_configuration, Prelude.Reg (Prelude.Bit 32)),
// (interrupt_status, Prelude.Reg (Prelude.Bit 32)),
// (interrupt_mask, Prelude.Reg (Prelude.Bit 32)),
// (interrupt_clear, Prelude.Reg (Prelude.Bit 32)),
// (_x2438,
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32)) ->
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32))),
// (_x2430,
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32)) ->
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32))),
// (_x2422,
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32)) ->
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32))),
// (_x2414,
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32)) ->
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32))),
// (_x2406,
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32)) ->
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32))),
// (_x2398,
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32)) ->
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32))),
// (_x2390,
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32)) ->
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32))),
// (_x2382,
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32)) ->
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32))),
// (_x2374,
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32)) ->
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32))),
// (_x2366,
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32)) ->
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32))),
// (_x2358,
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32)) ->
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32))),
// (_x2350,
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32)) ->
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32))),
// (_x2342,
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32)) ->
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32))),
// (_x2334,
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32)) ->
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32))),
// (_x2326,
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32)) ->
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32))),
// (_x2318,
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32)) ->
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32))),
// (_x2310,
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32)) ->
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32))),
// (_x2302,
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32)) ->
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32))),
// (_x2294,
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32)) ->
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32))),
// (_x2286,
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32)) ->
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32))),
// (_x2278,
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32)) ->
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32))),
// (_x2270,
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32)) ->
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32))),
// (_x2262,
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32)) ->
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32))),
// (_x2254,
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32)) ->
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32))),
// (_x2246,
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32)) ->
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32))),
// (_x2238,
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32)) ->
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32))),
// (_x2230,
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32)) ->
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32))),
// (_x2222,
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32)) ->
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32))),
// (_x2214,
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32)) ->
//  Prelude.Module (case_bug.Interface_reg (Prelude.Bit 8) (Prelude.Bit 32)))]
//




