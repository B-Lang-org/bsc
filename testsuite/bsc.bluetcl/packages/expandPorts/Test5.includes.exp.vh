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
  //   result => method4               13   ActionValue#(Test5::TS)
  //   input  => method4_in1           32   Int#(32)
  wire   RDY_method4;
  wire   EN_method4;
  wire   [ 12 : 0 ] method4;
  wire   [ 2 : 0 ] method4_a;  // method4[12:10]
  wire   [ 3 : 0 ] method4_b;  // method4[9:6]
  wire   [ 5 : 0 ] method4_c;  // method4[5:0]
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
  //   input  => method6_in1           13   Test5::TS
  wire   RDY_method6;
  wire   [ 31 : 0 ] method6;
  wire   [ 12 : 0 ] method6_in1;
  wire   [ 2 : 0 ] method6_in1_a;
  wire   [ 3 : 0 ] method6_in1_b;
  wire   [ 5 : 0 ] method6_in1_c;

  // ====================
  // Method = method7
  //   ready  => RDY_method7            1   Bit#(1)
  //   result => method7               13   Test5::TS
  wire   RDY_method7;
  wire   [ 12 : 0 ] method7;
  wire   [ 2 : 0 ] method7_a;  // method7[12:10]
  wire   [ 3 : 0 ] method7_b;  // method7[9:6]
  wire   [ 5 : 0 ] method7_c;  // method7[5:0]

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

  // ====================
  // Method = method10
  //   ready  => RDY_method10           1   Bit#(1)
  //   result => method10              39   {Vector::Vector#(3, Test5::TS)}
  wire   RDY_method10;
  wire   [ 38 : 0 ] method10;
  wire   [ 2 : 0 ] method10_0_a;  // method10[38:36]
  wire   [ 3 : 0 ] method10_0_b;  // method10[35:32]
  wire   [ 5 : 0 ] method10_0_c;  // method10[31:26]
  wire   [ 2 : 0 ] method10_1_a;  // method10[25:23]
  wire   [ 3 : 0 ] method10_1_b;  // method10[22:19]
  wire   [ 5 : 0 ] method10_1_c;  // method10[18:13]
  wire   [ 2 : 0 ] method10_2_a;  // method10[12:10]
  wire   [ 3 : 0 ] method10_2_b;  // method10[9:6]
  wire   [ 5 : 0 ] method10_2_c;  // method10[5:0]

  // ====================
  // Method = method20
  //   ready  => RDY_method20           1   Bit#(1)
  //   result => method20               4   Test5::TEnum
  wire   RDY_method20;
  wire   [ 3 : 0 ] method20;


`ifndef __EXPANDPORTS_NO_RENAMES__
  assign method4_a = method4[12:10];
  assign method4_b = method4[9:6];
  assign method4_c = method4[5:0];
  assign method6_in1[12:10] = method6_in1_a;
  assign method6_in1[9:6] = method6_in1_b;
  assign method6_in1[5:0] = method6_in1_c;
  assign method7_a = method7[12:10];
  assign method7_b = method7[9:6];
  assign method7_c = method7[5:0];
  assign method10_0_a = method10[38:36];
  assign method10_0_b = method10[35:32];
  assign method10_0_c = method10[31:26];
  assign method10_1_a = method10[25:23];
  assign method10_1_b = method10[22:19];
  assign method10_1_c = method10[18:13];
  assign method10_2_a = method10[12:10];
  assign method10_2_b = method10[9:6];
  assign method10_2_c = method10[5:0];
`endif

`ifndef __EXPANDPORTS_DONT_CREATE_DUT__
  mkTest5 _mkTest5 ( 
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
   .method9_in1( method9_in1 ),
   .RDY_method10( RDY_method10 ),
   .method10( method10 ),
   .RDY_method20( RDY_method20 ),
   .method20( method20 )
  );
`endif
