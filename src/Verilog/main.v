
`ifdef BSV_NO_MAIN_V
`else

`ifdef BSV_ASSIGNMENT_DELAY
`else
  `define BSV_ASSIGNMENT_DELAY
`endif

`ifdef BSV_POSITIVE_RESET
  `define BSV_RESET_VALUE 1'b1
  `define BSV_RESET_EDGE posedge
`else
  `define BSV_RESET_VALUE 1'b0
  `define BSV_RESET_EDGE negedge
`endif

`ifdef BSV_RESET_NAME
`else
 `define BSV_RESET_NAME RST_N
`endif

`ifdef BSV_TIMESCALE
 `timescale `BSV_TIMESCALE
`endif

module main();

   reg CLK;
   // reg CLK_GATE;
   reg RST;
   reg [31:0] cycle;
   reg        do_vcd;
   reg        do_fsdb;
   reg        do_fst;
   reg        do_cycles;

   `TOP top(.CLK(CLK), /* .CLK_GATE(CLK_GATE), */ .`BSV_RESET_NAME(RST));

// For Sce-Mi linkage, insert code here
`ifdef BSV_SCEMI_LINK
`include `BSV_SCEMI_LINK
`endif

`ifdef BSV_DUMP_LEVEL
`else
 `define BSV_DUMP_LEVEL 0
`endif

`ifdef BSV_DUMP_TOP
`else
 `define BSV_DUMP_TOP main
`endif

   reg [8*256:1] filename;

   initial begin
      // CLK_GATE = 1'b1;
      // CLK = 1'b0;    // This line will cause a neg edge of clk at t=0!
      // RST = !`BSV_RESET_VALUE'b0;  // This needs #0, to allow always blocks to wait
      cycle = 0;

      do_vcd    = $test$plusargs("bscvcd") ;
      do_fst    = $test$plusargs("bscfst") ;
      do_fsdb   = $test$plusargs("bscfsdb") ;
      do_cycles = $test$plusargs("bsccycle") ;

      if ($value$plusargs("bscvcd=%s", filename))
	do_vcd = 1; // avoids bug in cvc
      else if (do_vcd)
	filename = "dump.vcd";

      if ($value$plusargs("bscfsdb=%s", filename))
	do_fsdb = 1; // avoids bug in cvc
      else if (do_fsdb)
	filename = "dump.fsdb";

`ifdef BSC_FSDB
      if (do_fsdb) begin
         $fsdbDumpfile(filename);
         $fsdbDumpvars(`BSV_DUMP_LEVEL, `BSV_DUMP_TOP);
      end
`else

//      if (do_fst && ! do_vcd) begin
//         $dumpfile("|vcd2fst -F -f dump.fst -");
//         $dumpvars(`BSV_DUMP_LEVEL, `BSV_DUMP_TOP);
//      end

      if (do_vcd) begin
         $dumpfile(filename);
         $dumpvars(`BSV_DUMP_LEVEL, `BSV_DUMP_TOP);
      end

`endif

      #0
      RST = `BSV_RESET_VALUE;
      #1;
      CLK = 1'b1;
      // $display("reset");
      #1;
      RST = !`BSV_RESET_VALUE;
      // $display("reset done");
      //  #200010;
      //  $finish;
   end

`ifndef NO_CLOCK // for cosim
   always
     begin
        #1
        if (do_cycles)
          $display("cycle %0d", cycle) ;
        cycle = cycle + 1 ;
        #4;
        CLK = 1'b0 ;
        #5;
        CLK = 1'b1 ;
     end // always begin
`endif //  `ifndef NO_CLOCK


endmodule

`endif
