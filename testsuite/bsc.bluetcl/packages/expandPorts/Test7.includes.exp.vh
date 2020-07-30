// autocreated by expandPorts.tcl 2.0 and portUtil.tcl 2.0

  wire   CLK_c1;
  wire   [ 3 : 0 ] pIn;
  wire   CLK;
  wire   RST_N;
  // ====================
  // Method = ifcA_method1
  //   ready  => RDY_ifcA_method1       1   Bit#(1)
  //   enable => EN_ifcA_method1        1   Bit#(1)
  //   input  => ifcA_method1_in1      32   Int#(32)
  //   input  => ifcA_method1_in2      32   Int#(32)
  wire   RDY_ifcA_method1;
  wire   EN_ifcA_method1;
  wire   [ 31 : 0 ] ifcA_method1_in1;
  wire   [ 31 : 0 ] ifcA_method1_in2;

  // ====================
  // Method = ifcA_method2
  //   ready  => RDY_ifcA_method2       1   Bit#(1)
  //   result => ifcA_method2          32   Int#(32)
  //   input  => ifcA_method2_in1      32   Int#(32)
  //   input  => ifcA_method2_in2      32   Int#(32)
  wire   RDY_ifcA_method2;
  wire   [ 31 : 0 ] ifcA_method2;
  wire   [ 31 : 0 ] ifcA_method2_in1;
  wire   [ 31 : 0 ] ifcA_method2_in2;

  // ====================
  // Method = ifcA_method3
  //   ready  => RDY_ifcA_method3       1   Bit#(1)
  //   result => ifcA_method3          32   Int#(32)
  wire   RDY_ifcA_method3;
  wire   [ 31 : 0 ] ifcA_method3;

  // ====================
  // Method = ifcA_method4
  //   ready  => RDY_ifcA_method4       1   Bit#(1)
  //   enable => EN_ifcA_method4        1   Bit#(1)
  //   result => ifcA_method4          32   ActionValue#(Int#(32))
  //   input  => ifcA_method4_in1      32   Int#(32)
  wire   RDY_ifcA_method4;
  wire   EN_ifcA_method4;
  wire   [ 31 : 0 ] ifcA_method4;
  wire   [ 31 : 0 ] ifcA_method4_in1;

  // ====================
  // Method = ifcA_method5
  //   ready  => RDY_ifcA_method5       1   Bit#(1)
  //   enable => EN_ifcA_method5        1   Bit#(1)
  //   input  => ifcA_method5_in1       4   Bit#(4)
  wire   RDY_ifcA_method5;
  wire   EN_ifcA_method5;
  wire   [ 3 : 0 ] ifcA_method5_in1;

  // ====================
  // Method = ifcA_method6
  //   ready  => RDY_ifcA_method6       1   Bit#(1)
  //   result => ifcA_method6          32   Int#(32)
  //   input  => ifcA_method6_in1      12   Test7::TS
  wire   RDY_ifcA_method6;
  wire   [ 31 : 0 ] ifcA_method6;
  wire   [ 11 : 0 ] ifcA_method6_in1;
  wire   [ 3 : 0 ] ifcA_method6_in1_a;
  wire   [ 3 : 0 ] ifcA_method6_in1_b;
  wire   [ 3 : 0 ] ifcA_method6_in1_c;

  // ====================
  // Method = ifcA_method7
  //   ready  => RDY_ifcA_method7       1   Bit#(1)
  //   result => ifcA_method7          12   Test7::TS
  wire   RDY_ifcA_method7;
  wire   [ 11 : 0 ] ifcA_method7;
  wire   [ 3 : 0 ] ifcA_method7_a;  // ifcA_method7[11:8]
  wire   [ 3 : 0 ] ifcA_method7_b;  // ifcA_method7[7:4]
  wire   [ 3 : 0 ] ifcA_method7_c;  // ifcA_method7[3:0]

  // ====================
  // Method = ifcA_method8
  //   ready  => RDY_ifcA_method8       1   Bit#(1)
  //   enable => EN_ifcA_method8        1   Bit#(1)
  //   result => ifcA_method8           4   ActionValue#(Bit#(4))
  wire   RDY_ifcA_method8;
  wire   EN_ifcA_method8;
  wire   [ 3 : 0 ] ifcA_method8;

  // ====================
  // Method = ifcA_method9
  //   ready  => RDY_ifcA_method9       1   Bit#(1)
  //   enable => EN_ifcA_method9        1   Bit#(1)
  //   result => ifcA_method9           4   ActionValue#(Bit#(4))
  //   input  => ifcA_method9_in1       4   Bit#(4)
  wire   RDY_ifcA_method9;
  wire   EN_ifcA_method9;
  wire   [ 3 : 0 ] ifcA_method9;
  wire   [ 3 : 0 ] ifcA_method9_in1;

  // ====================
  // Method = ifcB_method1
  //   ready  => RDY_ifcB_method1       1   Bit#(1)
  //   enable => EN_ifcB_method1        1   Bit#(1)
  //   input  => ifcB_method1_in1      32   Int#(32)
  //   input  => ifcB_method1_in2      32   Int#(32)
  wire   RDY_ifcB_method1;
  wire   EN_ifcB_method1;
  wire   [ 31 : 0 ] ifcB_method1_in1;
  wire   [ 31 : 0 ] ifcB_method1_in2;

  // ====================
  // Method = ifcB_method2
  //   ready  => RDY_ifcB_method2       1   Bit#(1)
  //   result => ifcB_method2          32   Int#(32)
  //   input  => ifcB_method2_in1      32   Int#(32)
  //   input  => ifcB_method2_in2      32   Int#(32)
  wire   RDY_ifcB_method2;
  wire   [ 31 : 0 ] ifcB_method2;
  wire   [ 31 : 0 ] ifcB_method2_in1;
  wire   [ 31 : 0 ] ifcB_method2_in2;

  // ====================
  // Method = ifcB_method3
  //   ready  => RDY_ifcB_method3       1   Bit#(1)
  //   result => ifcB_method3          32   Int#(32)
  wire   RDY_ifcB_method3;
  wire   [ 31 : 0 ] ifcB_method3;

  // ====================
  // Method = ifcB_method4
  //   ready  => RDY_ifcB_method4       1   Bit#(1)
  //   enable => EN_ifcB_method4        1   Bit#(1)
  //   result => ifcB_method4          32   ActionValue#(Int#(32))
  //   input  => ifcB_method4_in1      32   Int#(32)
  wire   RDY_ifcB_method4;
  wire   EN_ifcB_method4;
  wire   [ 31 : 0 ] ifcB_method4;
  wire   [ 31 : 0 ] ifcB_method4_in1;

  // ====================
  // Method = ifcB_method5
  //   ready  => RDY_ifcB_method5       1   Bit#(1)
  //   enable => EN_ifcB_method5        1   Bit#(1)
  //   input  => ifcB_method5_in1       4   Bit#(4)
  wire   RDY_ifcB_method5;
  wire   EN_ifcB_method5;
  wire   [ 3 : 0 ] ifcB_method5_in1;

  // ====================
  // Method = ifcB_method6
  //   ready  => RDY_ifcB_method6       1   Bit#(1)
  //   result => ifcB_method6          32   Int#(32)
  //   input  => ifcB_method6_in1      12   Test7::TS
  wire   RDY_ifcB_method6;
  wire   [ 31 : 0 ] ifcB_method6;
  wire   [ 11 : 0 ] ifcB_method6_in1;
  wire   [ 3 : 0 ] ifcB_method6_in1_a;
  wire   [ 3 : 0 ] ifcB_method6_in1_b;
  wire   [ 3 : 0 ] ifcB_method6_in1_c;

  // ====================
  // Method = ifcB_method7
  //   ready  => RDY_ifcB_method7       1   Bit#(1)
  //   result => ifcB_method7          12   Test7::TS
  wire   RDY_ifcB_method7;
  wire   [ 11 : 0 ] ifcB_method7;
  wire   [ 3 : 0 ] ifcB_method7_a;  // ifcB_method7[11:8]
  wire   [ 3 : 0 ] ifcB_method7_b;  // ifcB_method7[7:4]
  wire   [ 3 : 0 ] ifcB_method7_c;  // ifcB_method7[3:0]

  // ====================
  // Method = ifcB_method8
  //   ready  => RDY_ifcB_method8       1   Bit#(1)
  //   enable => EN_ifcB_method8        1   Bit#(1)
  //   result => ifcB_method8           4   ActionValue#(Bit#(4))
  wire   RDY_ifcB_method8;
  wire   EN_ifcB_method8;
  wire   [ 3 : 0 ] ifcB_method8;

  // ====================
  // Method = ifcB_method9
  //   ready  => RDY_ifcB_method9       1   Bit#(1)
  //   enable => EN_ifcB_method9        1   Bit#(1)
  //   result => ifcB_method9           4   ActionValue#(Bit#(4))
  //   input  => ifcB_method9_in1       4   Bit#(4)
  wire   RDY_ifcB_method9;
  wire   EN_ifcB_method9;
  wire   [ 3 : 0 ] ifcB_method9;
  wire   [ 3 : 0 ] ifcB_method9_in1;


`ifndef __EXPANDPORTS_NO_RENAMES__
  assign ifcA_method6_in1[11:8] = ifcA_method6_in1_a;
  assign ifcA_method6_in1[7:4] = ifcA_method6_in1_b;
  assign ifcA_method6_in1[3:0] = ifcA_method6_in1_c;
  assign ifcA_method7_a = ifcA_method7[11:8];
  assign ifcA_method7_b = ifcA_method7[7:4];
  assign ifcA_method7_c = ifcA_method7[3:0];
  assign ifcB_method6_in1[11:8] = ifcB_method6_in1_a;
  assign ifcB_method6_in1[7:4] = ifcB_method6_in1_b;
  assign ifcB_method6_in1[3:0] = ifcB_method6_in1_c;
  assign ifcB_method7_a = ifcB_method7[11:8];
  assign ifcB_method7_b = ifcB_method7[7:4];
  assign ifcB_method7_c = ifcB_method7[3:0];
`endif

`ifndef __EXPANDPORTS_DONT_CREATE_DUT__
  mkTest7 _mkTest7 ( 
   .CLK_c1( CLK_c1 ),
   .pIn( pIn ),
   .CLK( CLK ),
   .RST_N( RST_N ),
   .RDY_ifcA_method1( RDY_ifcA_method1 ),
   .EN_ifcA_method1( EN_ifcA_method1 ),
   .ifcA_method1_in1( ifcA_method1_in1 ),
   .ifcA_method1_in2( ifcA_method1_in2 ),
   .RDY_ifcA_method2( RDY_ifcA_method2 ),
   .ifcA_method2( ifcA_method2 ),
   .ifcA_method2_in1( ifcA_method2_in1 ),
   .ifcA_method2_in2( ifcA_method2_in2 ),
   .RDY_ifcA_method3( RDY_ifcA_method3 ),
   .ifcA_method3( ifcA_method3 ),
   .RDY_ifcA_method4( RDY_ifcA_method4 ),
   .EN_ifcA_method4( EN_ifcA_method4 ),
   .ifcA_method4( ifcA_method4 ),
   .ifcA_method4_in1( ifcA_method4_in1 ),
   .RDY_ifcA_method5( RDY_ifcA_method5 ),
   .EN_ifcA_method5( EN_ifcA_method5 ),
   .ifcA_method5_in1( ifcA_method5_in1 ),
   .RDY_ifcA_method6( RDY_ifcA_method6 ),
   .ifcA_method6( ifcA_method6 ),
   .ifcA_method6_in1( ifcA_method6_in1 ),
   .RDY_ifcA_method7( RDY_ifcA_method7 ),
   .ifcA_method7( ifcA_method7 ),
   .RDY_ifcA_method8( RDY_ifcA_method8 ),
   .EN_ifcA_method8( EN_ifcA_method8 ),
   .ifcA_method8( ifcA_method8 ),
   .RDY_ifcA_method9( RDY_ifcA_method9 ),
   .EN_ifcA_method9( EN_ifcA_method9 ),
   .ifcA_method9( ifcA_method9 ),
   .ifcA_method9_in1( ifcA_method9_in1 ),
   .RDY_ifcB_method1( RDY_ifcB_method1 ),
   .EN_ifcB_method1( EN_ifcB_method1 ),
   .ifcB_method1_in1( ifcB_method1_in1 ),
   .ifcB_method1_in2( ifcB_method1_in2 ),
   .RDY_ifcB_method2( RDY_ifcB_method2 ),
   .ifcB_method2( ifcB_method2 ),
   .ifcB_method2_in1( ifcB_method2_in1 ),
   .ifcB_method2_in2( ifcB_method2_in2 ),
   .RDY_ifcB_method3( RDY_ifcB_method3 ),
   .ifcB_method3( ifcB_method3 ),
   .RDY_ifcB_method4( RDY_ifcB_method4 ),
   .EN_ifcB_method4( EN_ifcB_method4 ),
   .ifcB_method4( ifcB_method4 ),
   .ifcB_method4_in1( ifcB_method4_in1 ),
   .RDY_ifcB_method5( RDY_ifcB_method5 ),
   .EN_ifcB_method5( EN_ifcB_method5 ),
   .ifcB_method5_in1( ifcB_method5_in1 ),
   .RDY_ifcB_method6( RDY_ifcB_method6 ),
   .ifcB_method6( ifcB_method6 ),
   .ifcB_method6_in1( ifcB_method6_in1 ),
   .RDY_ifcB_method7( RDY_ifcB_method7 ),
   .ifcB_method7( ifcB_method7 ),
   .RDY_ifcB_method8( RDY_ifcB_method8 ),
   .EN_ifcB_method8( EN_ifcB_method8 ),
   .ifcB_method8( ifcB_method8 ),
   .RDY_ifcB_method9( RDY_ifcB_method9 ),
   .EN_ifcB_method9( EN_ifcB_method9 ),
   .ifcB_method9( ifcB_method9 ),
   .ifcB_method9_in1( ifcB_method9_in1 )
  );
`endif
