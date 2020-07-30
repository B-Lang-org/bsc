
import SyncFIFOSlow::*;
import Clocks::*;

typedef enum {Start, StateA, StateB} State
    deriving (Bits, Eq);

function ActionValue#(Bit#(64)) adjusted_time(Bit#(64) lag);
    actionvalue
        let t <- $time;
        if (genVerilog)
            return (t + lag);
        else
            return t;
    endactionvalue
endfunction

function Action push_print (Bit#(32) a);
    action
        $display(adjusted_time(34), "\tPushing Data=%d", a);
    endaction
endfunction: push_print

function Action pop_print;
    action
        $display(adjusted_time(134), "\tPopping Data\n");
    endaction
endfunction: pop_print

module mkTestbench_write_slow_read_fast(Empty);

function Action my_print (Bit#(8) expected,Bit#(8) actual, Bool cond, Reg#(Bool) t_pass);
    action
        case(cond)
        True:
            if (actual==expected) 
                $display(adjusted_time(134), "\tData Match, Actual = %d",actual); 
            else begin
                t_pass <= False;
                $display(adjusted_time(134), "\tData Mismatch, Actual = %d, Expected = %d",actual,expected);                           
            end
        False: 
            $display(adjusted_time(134), "\tActual = %d, Expected = nothing",actual);
        endcase
    endaction
endfunction: my_print

Clock           wr_clk();
mkAbsoluteClock t_wr_clk(7, 67, wr_clk);

Reset              wr_rst();
mkInitialReset#(2) t_wr_rst(wr_rst, clocked_by wr_clk);

SyncFIFOSlow_IFC            fifo();
mkSyncFIFOSlow              t_fifo(fifo, clocked_by wr_clk, reset_by wr_rst);

Reg#(Bool)      test_pass();
mkReg#(True)    t_test_pass(test_pass, clocked_by fifo.rd_clk_o, reset_by fifo.rd_rst_o);

Reg#(Bit#(32))  wr_cnt();
mkReg#(0)       t_wr_cnt(wr_cnt, clocked_by wr_clk, reset_by wr_rst);

Reg#(Bit#(32))  rd_cnt();
mkReg#(0)       t_rd_cnt(rd_cnt, clocked_by fifo.rd_clk_o, reset_by fifo.rd_rst_o);

SyncBitIfc#(Bit#(1))  rd_start();
mkSyncBit             i_rd_start(wr_clk, wr_rst, fifo.rd_clk_o, rd_start);

SyncBitIfc#(Bit#(1))  sim_end();
mkSyncBit             i_sim_end(fifo.rd_clk_o, fifo.rd_rst_o, wr_clk, sim_end);

Reg#(State)     state();
mkReg#(Start)   t_state(state, clocked_by wr_clk, reset_by wr_rst);

// quick and dirty counter
// to wait long enough until the DUT is out of reset before starting the test
Reg#(Bit#(8))   init_count();
mkReg#(12)      t_init_count(init_count, clocked_by wr_clk, reset_by wr_rst);

rule fromInitial (state == Start);
   if (init_count == 0) begin
      state   <= StateA;
      wr_cnt  <= 0;
   end
   else
      init_count <= init_count - 1;
endrule
              
rule fromStateA_rl1 (state ==StateA && wr_cnt < 16); //Write 16 cycles, Read 16 cycles 
            wr_cnt <= wr_cnt + 1;
            fifo.push(wr_cnt[7:0], 1'b1);  //Push data values 0 to 15
            push_print(wr_cnt);
	    if (wr_cnt == 15)
		begin
		rd_start.send(1'b1);
		state <= StateB;
		end
endrule
rule fromStateA_rl2 (rd_cnt < 16 && rd_start.read == 1);
            rd_cnt <= rd_cnt + 1;
            fifo.pop(1'b1);
            pop_print;
            if (rd_cnt > 0) 
                my_print(rd_cnt[7:0] - 1, fifo.data_out, True, test_pass);
	    sim_end.send(1'b1);
endrule
rule fromStateA_rl3 (rd_cnt == 16);
            rd_cnt <= 0;
            my_print(rd_cnt[7:0]-1, fifo.data_out, True, test_pass);
	    if (test_pass)  
                $display("\tPassed Fifo Test.");
            else 
                $display("\tFailed Fifo Test.");
	    $finish(0);
endrule

endmodule: mkTestbench_write_slow_read_fast
