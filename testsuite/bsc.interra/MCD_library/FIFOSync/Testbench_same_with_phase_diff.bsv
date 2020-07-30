
import Design::*;
import Clocks::*;
import Disp::*;

// Clock periods
Integer wrp = 17;
Integer rdp = 17;

typedef enum {Start, StateA, StateB} State
    deriving (Bits, Eq);

module mkTestbench_same_with_phase_diff(Empty);

Clock           wr_clk();
mkAbsoluteClock t_wr_clk(15, wrp, wr_clk);

Clock           rd_clk();
mkAbsoluteClock t_rd_clk(2, rdp, rd_clk);

Reset              wr_rst();
mkInitialReset#(2) t_wr_rst(wr_rst, clocked_by wr_clk);

Reset              rd_rst();
mkInitialReset#(2) t_rd_rst(rd_rst, clocked_by rd_clk);

Design_IFC                fifo();
mkDesign#(rd_clk, rd_rst) t_fifo(fifo, clocked_by wr_clk, reset_by wr_rst);

Reg#(Bool)      test_pass();
mkReg#(True)    t_test_pass(test_pass, clocked_by rd_clk, reset_by rd_rst);

Reg#(Bit#(32))  wr_cnt();
mkReg#(0)       t_wr_cnt(wr_cnt, clocked_by wr_clk, reset_by wr_rst);

Reg#(Bit#(32))  rd_cnt();
mkReg#(0)       t_rd_cnt(rd_cnt, clocked_by rd_clk, reset_by rd_rst);

SyncBitIfc#(Bool)      rd_start();
mkSyncBit       i_rd_start(wr_clk, wr_rst, rd_clk, rd_start);

SyncBitIfc#(Bool)      sim_end();
mkSyncBit       i_sim_end(rd_clk, rd_rst, wr_clk, sim_end);

Reg#(State)     state();
mkReg#(Start)   t_state(state, clocked_by wr_clk, reset_by wr_rst);

rule fromInitial (state == Start);
    action
        state   <= StateA;
        wr_cnt <= 0;
    endaction
endrule
              
rule fromStateA_rl1 (state ==StateA && wr_cnt < 16); //Write 16 cycles, Read 16 cycles 
            wr_cnt <= wr_cnt + 1;
            fifo.push(wr_cnt[7:0], 1'b1);  //Push data values 0 to 15
            push_print(wrp, wr_cnt);
	    if (wr_cnt == 15)
		begin
		rd_start.send(True);
		state <= StateB;
		end
endrule
rule fromStateA_rl2 (rd_cnt < 16 && rd_start.read );
            rd_cnt <= rd_cnt + 1;
            fifo.pop(1'b1);
            pop_print(rdp);
            if (rd_cnt > 0) 
                my_print(rdp, rd_cnt[7:0] - 1, fifo.data_out, True, test_pass);
	    sim_end.send(True); // XXX Not read.
endrule
rule fromStateA_rl3 (rd_cnt == 16);
            rd_cnt <= 0;
            my_print(rdp, rd_cnt[7:0]-1, fifo.data_out, True, test_pass);
	    if (test_pass)  
                $display("\tPassed Fifo Test.");
            else 
                $display("\tFailed Fifo Test.");
	    $finish(0);
endrule

endmodule: mkTestbench_same_with_phase_diff
  





