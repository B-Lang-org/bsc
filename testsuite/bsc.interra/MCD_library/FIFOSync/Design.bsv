//Testcase for clock domain crossing using Synchronous FIFO : MCD
//Module's input is write and data input (linked with write clock)
//Also it has input read (linked with read clock)
//Data is written in accordance with write into FIFO clocked with
//write clock.
//Read occurs in accordance with read linked to read clock.

import Clocks::*;

            
interface Design_IFC;
    method Action   push        (Bit#(8) data_in, Bit#(1) write);
    method Action   pop         (Bit#(1) read);
    method Bit#(8)  data_out    ();
endinterface: Design_IFC

(*
    always_enabled,
    CLK = "wr_clk",
    RST_N = "wr_rst"
*)

module mkDesign (Clock rd_clk, Reset rd_rst, Design_IFC ifc);
        
    SyncFIFOIfc#(Bit#(8))     datafifo();
    mkSyncFIFOFromCC#(16)     t_datafifo(rd_clk, datafifo);

    Reg#(Bit#(8))       data_out_reg();
    mkReg#(0)           t_data_out_reg(data_out_reg, clocked_by rd_clk, reset_by rd_rst);

    method push(in_data, w);
        action
            if (w == 1'b1) 
                datafifo.enq(in_data);
            else
                noAction;
        endaction
    endmethod: push
   
    method pop(r);
        action
            if(r == 1'b1) begin
                datafifo.deq();    
                data_out_reg <= datafifo.first;
            end   
        endaction
    endmethod: pop

    method data_out();
        data_out = data_out_reg;
    endmethod: data_out

endmodule: mkDesign 
