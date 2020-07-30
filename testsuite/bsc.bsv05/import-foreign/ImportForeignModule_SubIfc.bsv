// Test that subinterfaces can be referenced by hierarchical (dot) notation

interface ClocksOut;
   interface Clock clock_out_1;
   interface Clock clock_out_2;
endinterface

interface ResetsOut;
   interface Reset rst_out_1;
   interface Reset rst_out_2;
endinterface

interface TwoReg ;
   interface Reg#(Bool) r1 ;
   interface Reg#(Bool) r2 ;
   interface ClocksOut  cs ;
   interface ResetsOut  rs ;
endinterface

import "BVI" MOD =
module mkTwoReg ( Clock aClk, 
		  Clock bClk,
		  TwoReg ifcout ) ;

   default_clock no_clock ;
   no_reset ;

   input_clock  aClk(A_CLK, A_CLKGATE) = aClk ;
   input_clock  bClk(B_CLK, B_CLKGATE) = bClk ;

   interface ClocksOut cs;
      output_clock clock_out_1 (CLK_OUT_1);
      output_clock clock_out_2 (CLK_OUT_2);
   endinterface

   interface ResetsOut rs;
      // test dotted clocked_by
      output_reset rst_out_1 (RST_OUT_1_N) clocked_by (cs.clock_out_1);
      output_reset rst_out_2 (RST_OUT_2_N) clocked_by (cs.clock_out_2);
   endinterface

   interface Reg r1;
      method _write(D_IN_1) enable(EN_1) clocked_by(aClk) reset_by(no_reset);
      method Q_OUT_1 _read clocked_by(aClk) reset_by(no_reset);
   endinterface

   interface Reg r2;
      // use hierarchical names in "clocked_by" and "reset_by"
      method _write(D_IN_2) enable(EN_2)
	 clocked_by(cs.clock_out_1) reset_by(rs.rst_out_1);
      method Q_OUT_2 _read
	 clocked_by(cs.clock_out_2) reset_by(rs.rst_out_2);
   endinterface

   // test ancestor and family statements for hierarchical clock names
   same_family (cs.clock_out_1, cs.clock_out_2);
   ancestor (aClk, cs.clock_out_1);

   // test schedule statements
   schedule r1._read SB r1._write ;
   schedule (r1._read, r2._read) CF (r1._read, r2._read) ;
endmodule

