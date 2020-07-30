//Testcase for clock domain crossing using Dual Port RAM (AsyncRAM) : MCD
//Module's input is write address and data input (linked with write clock)
//Also it has input read address (linked with read clock)
//Data is written in accordance with write address into a regfile clocked with
//write clock.
//Read occurs in accordance with read address linked to read clock. (dout port)

import Clocks::*;

interface Design_IFC;
  method Action write (Bit#(16) waddr, Bit#(8) din);
  method Action read (Bit#(16) raddr);
  method Bit#(8) dout();
endinterface : Design_IFC

(* 
   CLK = "rd_clk",
   RST_N = "rd_rst"
*)

module mkDesign (Clock wr_clk, Reset wr_rst, Design_IFC ifc);
      DualPortRamIfc#(Bit#(16), Bit#(8)) mem_array();
      mkDualRam                          t_mem_array(mem_array, clocked_by wr_clk, reset_by wr_rst);

      Reg#(Bit#(8))  dout_reg();
      mkReg#(0)      t_dout_reg(dout_reg);

      method Action write(waddr1, din1);
	mem_array.write(waddr1, din1);
      endmethod : write

      method Action read(raddr1);
	dout_reg <= mem_array.read(raddr1);
      endmethod : read

      method dout();
	dout = dout_reg;
      endmethod : dout
endmodule: mkDesign



