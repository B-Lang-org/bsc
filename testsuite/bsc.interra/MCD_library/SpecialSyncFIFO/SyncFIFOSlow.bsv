//Testcase for clock domain crossing using Special Synchronous FIFO(aligned edges) : MCD
//Module's input is write and data input (linked with write clock)
//Also it has input read (linked with read clock)
//Data is written in accordance with write into FIFO clocked with
//write clock.
//Read occurs in accordance with read linked to read clock.
//In this read clock is write clock divide by 4 using ClockDivider primitive of //Bluespec.

import Clocks::*;

            
interface SyncFIFOSlow_IFC;
    method Action   push        (Bit#(8) data_in, Bit#(1) write);
    method Action   pop         (Bit#(1) read);
    method Bit#(8)  data_out    ();
    interface Clock rd_clk_o;
    interface Reset rd_rst_o;
endinterface: SyncFIFOSlow_IFC

(*
    CLK = "wr_clk",
    RST_N = "wr_rst",
    synthesize
*)

module mkSyncFIFOSlow (SyncFIFOSlow_IFC ifc);
    Clock currClk <- exposeCurrentClock;

    ClockDividerIfc           div();
    mkClockDivider#(4)        t_div(div);

    Clock rd_clk = div.slowClock;

    Reset                 rd_rst();
    mkAsyncResetFromCR#(3) t_rd_rst(rd_clk, rd_rst);

    SyncFIFOIfc#(Bit#(8))     datafifo();
    mkSyncFIFOToSlow#(16)     t_datafifo(div, rd_rst, datafifo);

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

    interface Clock rd_clk_o = rd_clk;
    interface Clock rd_rst_o = rd_rst;

endmodule: mkSyncFIFOSlow 
