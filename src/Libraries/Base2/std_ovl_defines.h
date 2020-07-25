// Accellera Standard V1.5 Open Verification Library (OVL).
// Accellera Copyright (c) 2005. All rights reserved.

`ifdef OVL_STD_DEFINES_H
// do nothing
`else
`define OVL_STD_DEFINES_H

`define OVL_VERSION "V1.5"

`ifdef OVL_ASSERT_ON
  `ifdef OVL_PSL
     `ifdef OVL_VERILOG
        `undef OVL_PSL
     `endif
     `ifdef OVL_SVA
        `ifdef OVL_PSL
          `undef OVL_PSL
        `endif
     `endif
  `else
    `ifdef OVL_VERILOG
    `else
      `define OVL_VERILOG
    `endif
    `ifdef OVL_SVA
       `undef OVL_VERILOG
    `endif
  `endif
`endif

`ifdef OVL_COVER_ON
`ifdef OVL_PSL
     `ifdef OVL_VERILOG
        `undef OVL_PSL
     `endif
     `ifdef OVL_SVA
        `ifdef OVL_PSL
          `undef OVL_PSL
        `endif
     `endif
  `else
    `ifdef OVL_VERILOG
    `else
      `define OVL_VERILOG
    `endif
    `ifdef OVL_SVA
       `undef OVL_VERILOG
    `endif
  `endif
`endif

`ifdef OVL_ASSERT_ON
  `ifdef OVL_SHARED_CODE
  `else
    `define OVL_SHARED_CODE
  `endif
`else
  `ifdef OVL_COVER_ON
    `ifdef OVL_SHARED_CODE
    `else
      `define OVL_SHARED_CODE
    `endif
  `endif
`endif

// specifying interface for System Verilog

`ifdef OVL_SVA_INTERFACE
  `define module interface
  `define endmodule endinterface
`else
  `define module module
  `define endmodule endmodule
`endif

// Selecting global reset or local reset for the checker reset signal

`ifdef OVL_GLOBAL_RESET
  `define OVL_RESET_SIGNAL `OVL_GLOBAL_RESET
`else
  `define OVL_RESET_SIGNAL reset_n
`endif

// active edges

`define OVL_NOEDGE 0
`define OVL_POSEDGE 1
`define OVL_NEGEDGE 2
`define OVL_ANYEDGE 3

// severity levels

`define OVL_FATAL   0
`define OVL_ERROR   1
`define OVL_WARNING 2
`define OVL_INFO    3

// coverage levels

`define OVL_COVER_NONE      0
`define OVL_COVER_SANITY    1
`define OVL_COVER_BASIC     2
`define OVL_COVER_CORNER    4
`define OVL_COVER_STATISTIC 8
// `define OVL_COVER_ALL       {32{1'b1}}
`define OVL_COVER_ALL       32'hFFFFFFFF

// property type

`define OVL_ASSERT 0
`define OVL_ASSUME 1
`define OVL_IGNORE 2

// necessary condition

`define OVL_TRIGGER_ON_MOST_PIPE    0
`define OVL_TRIGGER_ON_FIRST_PIPE   1
`define OVL_TRIGGER_ON_FIRST_NOPIPE 2

// action on new start

`define OVL_IGNORE_NEW_START   0
`define OVL_RESET_ON_NEW_START 1
`define OVL_ERROR_ON_NEW_START 2

// inactive levels

`define OVL_ALL_ZEROS 0
`define OVL_ALL_ONES  1
`define OVL_ONE_COLD  2

// Functions for logarithmic calculation

`define log(n) ((n) <= (1<<0) ? 1 :\
                (n) <= (1<<1) ? 1 :\
                (n) <= (1<<2) ? 2 :\
                (n) <= (1<<3) ? 3 :\
                (n) <= (1<<4) ? 4 :\
                (n) <= (1<<5) ? 5 :\
                (n) <= (1<<6) ? 6 :\
                (n) <= (1<<7) ? 7 :\
                (n) <= (1<<8) ? 8 :\
                (n) <= (1<<9) ? 9 :\
                (n) <= (1<<10) ? 10 :\
                (n) <= (1<<11) ? 11 :\
                (n) <= (1<<12) ? 12 :\
                (n) <= (1<<13) ? 13 :\
                (n) <= (1<<14) ? 14 :\
                (n) <= (1<<15) ? 15 :\
                (n) <= (1<<16) ? 16 :\
                (n) <= (1<<17) ? 17 :\
                (n) <= (1<<18) ? 18 :\
                (n) <= (1<<19) ? 19 :\
                (n) <= (1<<20) ? 20 :\
                (n) <= (1<<21) ? 21 :\
                (n) <= (1<<22) ? 22 :\
                (n) <= (1<<23) ? 23 :\
                (n) <= (1<<24) ? 24 :\
                (n) <= (1<<25) ? 25 :\
                (n) <= (1<<26) ? 26 :\
                (n) <= (1<<27) ? 27 :\
                (n) <= (1<<28) ? 28 :\
                (n) <= (1<<29) ? 29 :\
                (n) <= (1<<30) ? 30 :\
                (n) <= (1<<31) ? 31 : 32)

`endif // OVL_STD_DEFINES_H
