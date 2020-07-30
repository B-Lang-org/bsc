// autocreated by expandPorts.tcl 2.0 and portUtil.tcl 2.0

  wire   CLK;
  wire   RST_N;
  // ====================
  // Method = method1
  //   ready  => RDY_method1            1   Bit#(1)
  //   enable => EN_method1             1   Bit#(1)
  //   input  => method1_in1           32   Int#(32)
  //   input  => method1_in2           32   Int#(32)
  wire   RDY_method1;
  wire   EN_method1;
  wire   [ 31 : 0 ] method1_in1;
  wire   [ 31 : 0 ] method1_in2;

  // ====================
  // Method = method2
  //   ready  => RDY_method2            1   Bit#(1)
  //   result => method2               32   Int#(32)
  //   input  => method2_in1           32   Int#(32)
  //   input  => method2_in2           32   Int#(32)
  wire   RDY_method2;
  wire   [ 31 : 0 ] method2;
  wire   [ 31 : 0 ] method2_in1;
  wire   [ 31 : 0 ] method2_in2;

  // ====================
  // Method = method3
  //   ready  => RDY_method3            1   Bit#(1)
  //   result => method3               32   Int#(32)
  wire   RDY_method3;
  wire   [ 31 : 0 ] method3;

  // ====================
  // Method = method4
  //   ready  => RDY_method4            1   Bit#(1)
  //   enable => EN_method4             1   Bit#(1)
  //   result => method4               32   ActionValue#(Int#(32))
  //   input  => method4_in1           32   Int#(32)
  wire   RDY_method4;
  wire   EN_method4;
  wire   [ 31 : 0 ] method4;
  wire   [ 31 : 0 ] method4_in1;

  // ====================
  // Method = method5
  //   ready  => RDY_method5            1   Bit#(1)
  //   enable => EN_method5             1   Bit#(1)
  //   input  => method5_in1            4   Bit#(4)
  wire   RDY_method5;
  wire   EN_method5;
  wire   [ 3 : 0 ] method5_in1;

  // ====================
  // Method = method6
  //   ready  => RDY_method6            1   Bit#(1)
  //   result => method6               32   Int#(32)
  //   input  => method6_in1           12   Test1::TS
  wire   RDY_method6;
  wire   [ 31 : 0 ] method6;
  wire   [ 11 : 0 ] method6_in1;
  wire   [ 3 : 0 ] method6_in1_a;
  wire   [ 3 : 0 ] method6_in1_b;
  wire   [ 3 : 0 ] method6_in1_c;

  // ====================
  // Method = method7
  //   ready  => RDY_method7            1   Bit#(1)
  //   result => method7               12   Test1::TS
  wire   RDY_method7;
  wire   [ 11 : 0 ] method7;
  wire   [ 3 : 0 ] method7_a;  // method7[11:8]
  wire   [ 3 : 0 ] method7_b;  // method7[7:4]
  wire   [ 3 : 0 ] method7_c;  // method7[3:0]

  // ====================
  // Method = method8
  //   ready  => RDY_method8            1   Bit#(1)
  //   enable => EN_method8             1   Bit#(1)
  //   result => method8                4   ActionValue#(Bit#(4))
  wire   RDY_method8;
  wire   EN_method8;
  wire   [ 3 : 0 ] method8;

  // ====================
  // Method = method9
  //   ready  => RDY_method9            1   Bit#(1)
  //   enable => EN_method9             1   Bit#(1)
  //   result => method9                4   ActionValue#(Bit#(4))
  //   input  => method9_in1            4   Bit#(4)
  wire   RDY_method9;
  wire   EN_method9;
  wire   [ 3 : 0 ] method9;
  wire   [ 3 : 0 ] method9_in1;


`ifndef __EXPANDPORTS_NO_RENAMES__
  assign method6_in1[11:8] = method6_in1_a;
  assign method6_in1[7:4] = method6_in1_b;
  assign method6_in1[3:0] = method6_in1_c;
  assign method7_a = method7[11:8];
  assign method7_b = method7[7:4];
  assign method7_c = method7[3:0];
`endif

`ifndef __EXPANDPORTS_DONT_CREATE_DUT__
  mkTest1 _mkTest1 ( 
   .CLK( CLK ),
   .RST_N( RST_N ),
   .RDY_method1( RDY_method1 ),
   .EN_method1( EN_method1 ),
   .method1_in1( method1_in1 ),
   .method1_in2( method1_in2 ),
   .RDY_method2( RDY_method2 ),
   .method2( method2 ),
   .method2_in1( method2_in1 ),
   .method2_in2( method2_in2 ),
   .RDY_method3( RDY_method3 ),
   .method3( method3 ),
   .RDY_method4( RDY_method4 ),
   .EN_method4( EN_method4 ),
   .method4( method4 ),
   .method4_in1( method4_in1 ),
   .RDY_method5( RDY_method5 ),
   .EN_method5( EN_method5 ),
   .method5_in1( method5_in1 ),
   .RDY_method6( RDY_method6 ),
   .method6( method6 ),
   .method6_in1( method6_in1 ),
   .RDY_method7( RDY_method7 ),
   .method7( method7 ),
   .RDY_method8( RDY_method8 ),
   .EN_method8( EN_method8 ),
   .method8( method8 ),
   .RDY_method9( RDY_method9 ),
   .EN_method9( EN_method9 ),
   .method9( method9 ),
   .method9_in1( method9_in1 )
  );
`endif
