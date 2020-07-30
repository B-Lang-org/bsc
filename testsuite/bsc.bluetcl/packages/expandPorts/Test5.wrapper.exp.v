// autocreated by expandPorts.tcl 2.0 and portUtil.tcl 2.0
module mkTest5_expanded (
    CLK,
    RST_N,
    RDY_method1,
    EN_method1,
    method1_in1,
    method1_in2,
    RDY_method2,
    method2,
    method2_in1,
    method2_in2,
    RDY_method3,
    method3,
    RDY_method4,
    EN_method4,
    method4_a,
    method4_b,
    method4_c,
    method4_in1,
    RDY_method5,
    EN_method5,
    method5_in1,
    RDY_method6,
    method6,
    method6_in1_a,
    method6_in1_b,
    method6_in1_c,
    RDY_method7,
    method7_a,
    method7_b,
    method7_c,
    RDY_method8,
    EN_method8,
    method8,
    RDY_method9,
    EN_method9,
    method9,
    method9_in1,
    RDY_method10,
    method10_0_a,
    method10_0_b,
    method10_0_c,
    method10_1_a,
    method10_1_b,
    method10_1_c,
    method10_2_a,
    method10_2_b,
    method10_2_c,
    RDY_method20,
    method20 );

  input CLK;
  input RST_N;

  // ====================
  // Method = method1
  //   ready  => RDY_method1            1   Bit#(1)
  //   enable => EN_method1             1   Bit#(1)
  //   input  => method1_in1           32   Int#(32)
  //   input  => method1_in2           32   Int#(32)
  output  RDY_method1;
  input  EN_method1;
  input  [ 31 : 0 ] method1_in1;
  input  [ 31 : 0 ] method1_in2;

  // ====================
  // Method = method2
  //   ready  => RDY_method2            1   Bit#(1)
  //   result => method2               32   Int#(32)
  //   input  => method2_in1           32   Int#(32)
  //   input  => method2_in2           32   Int#(32)
  output  RDY_method2;
  output  [ 31 : 0 ] method2;
  input  [ 31 : 0 ] method2_in1;
  input  [ 31 : 0 ] method2_in2;

  // ====================
  // Method = method3
  //   ready  => RDY_method3            1   Bit#(1)
  //   result => method3               32   Int#(32)
  output  RDY_method3;
  output  [ 31 : 0 ] method3;

  // ====================
  // Method = method4
  //   ready  => RDY_method4            1   Bit#(1)
  //   enable => EN_method4             1   Bit#(1)
  //   result => method4               13   ActionValue#(Test5::TS)
  //   input  => method4_in1           32   Int#(32)
  output  RDY_method4;
  input  EN_method4;
  output  [ 2 : 0 ] method4_a;  // method4[12:10]
  output  [ 3 : 0 ] method4_b;  // method4[9:6]
  output  [ 5 : 0 ] method4_c;  // method4[5:0]
  input  [ 31 : 0 ] method4_in1;

  // ====================
  // Method = method5
  //   ready  => RDY_method5            1   Bit#(1)
  //   enable => EN_method5             1   Bit#(1)
  //   input  => method5_in1            4   Bit#(4)
  output  RDY_method5;
  input  EN_method5;
  input  [ 3 : 0 ] method5_in1;

  // ====================
  // Method = method6
  //   ready  => RDY_method6            1   Bit#(1)
  //   result => method6               32   Int#(32)
  //   input  => method6_in1           13   Test5::TS
  output  RDY_method6;
  output  [ 31 : 0 ] method6;
  input  [ 2 : 0 ] method6_in1_a;
  input  [ 3 : 0 ] method6_in1_b;
  input  [ 5 : 0 ] method6_in1_c;

  // ====================
  // Method = method7
  //   ready  => RDY_method7            1   Bit#(1)
  //   result => method7               13   Test5::TS
  output  RDY_method7;
  output  [ 2 : 0 ] method7_a;  // method7[12:10]
  output  [ 3 : 0 ] method7_b;  // method7[9:6]
  output  [ 5 : 0 ] method7_c;  // method7[5:0]

  // ====================
  // Method = method8
  //   ready  => RDY_method8            1   Bit#(1)
  //   enable => EN_method8             1   Bit#(1)
  //   result => method8                4   ActionValue#(Bit#(4))
  output  RDY_method8;
  input  EN_method8;
  output  [ 3 : 0 ] method8;

  // ====================
  // Method = method9
  //   ready  => RDY_method9            1   Bit#(1)
  //   enable => EN_method9             1   Bit#(1)
  //   result => method9                4   ActionValue#(Bit#(4))
  //   input  => method9_in1            4   Bit#(4)
  output  RDY_method9;
  input  EN_method9;
  output  [ 3 : 0 ] method9;
  input  [ 3 : 0 ] method9_in1;

  // ====================
  // Method = method10
  //   ready  => RDY_method10           1   Bit#(1)
  //   result => method10              39   {Vector::Vector#(3, Test5::TS)}
  output  RDY_method10;
  output  [ 2 : 0 ] method10_0_a;  // method10[38:36]
  output  [ 3 : 0 ] method10_0_b;  // method10[35:32]
  output  [ 5 : 0 ] method10_0_c;  // method10[31:26]
  output  [ 2 : 0 ] method10_1_a;  // method10[25:23]
  output  [ 3 : 0 ] method10_1_b;  // method10[22:19]
  output  [ 5 : 0 ] method10_1_c;  // method10[18:13]
  output  [ 2 : 0 ] method10_2_a;  // method10[12:10]
  output  [ 3 : 0 ] method10_2_b;  // method10[9:6]
  output  [ 5 : 0 ] method10_2_c;  // method10[5:0]

  // ====================
  // Method = method20
  //   ready  => RDY_method20           1   Bit#(1)
  //   result => method20               4   Test5::TEnum
  output  RDY_method20;
  output  [ 3 : 0 ] method20;


  wire   RDY_method1;
  wire   RDY_method2;
  wire   [ 31 : 0 ] method2;
  wire   RDY_method3;
  wire   [ 31 : 0 ] method3;
  wire   RDY_method4;
  wire   [ 2 : 0 ] method4_a;  // method4[12:10]
  wire   [ 3 : 0 ] method4_b;  // method4[9:6]
  wire   [ 5 : 0 ] method4_c;  // method4[5:0]
  wire   RDY_method5;
  wire   RDY_method6;
  wire   [ 31 : 0 ] method6;
  wire   RDY_method7;
  wire   [ 2 : 0 ] method7_a;  // method7[12:10]
  wire   [ 3 : 0 ] method7_b;  // method7[9:6]
  wire   [ 5 : 0 ] method7_c;  // method7[5:0]
  wire   RDY_method8;
  wire   [ 3 : 0 ] method8;
  wire   RDY_method9;
  wire   [ 3 : 0 ] method9;
  wire   RDY_method10;
  wire   [ 2 : 0 ] method10_0_a;  // method10[38:36]
  wire   [ 3 : 0 ] method10_0_b;  // method10[35:32]
  wire   [ 5 : 0 ] method10_0_c;  // method10[31:26]
  wire   [ 2 : 0 ] method10_1_a;  // method10[25:23]
  wire   [ 3 : 0 ] method10_1_b;  // method10[22:19]
  wire   [ 5 : 0 ] method10_1_c;  // method10[18:13]
  wire   [ 2 : 0 ] method10_2_a;  // method10[12:10]
  wire   [ 3 : 0 ] method10_2_b;  // method10[9:6]
  wire   [ 5 : 0 ] method10_2_c;  // method10[5:0]
  wire   RDY_method20;
  wire   [ 3 : 0 ] method20;

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
   .method4( { method4_a,method4_b,method4_c } ),
   .method4_in1( method4_in1 ),
   .RDY_method5( RDY_method5 ),
   .EN_method5( EN_method5 ),
   .method5_in1( method5_in1 ),
   .RDY_method6( RDY_method6 ),
   .method6( method6 ),
   .method6_in1( { method6_in1_a,method6_in1_b,method6_in1_c } ),
   .RDY_method7( RDY_method7 ),
   .method7( { method7_a,method7_b,method7_c } ),
   .RDY_method8( RDY_method8 ),
   .EN_method8( EN_method8 ),
   .method8( method8 ),
   .RDY_method9( RDY_method9 ),
   .EN_method9( EN_method9 ),
   .method9( method9 ),
   .method9_in1( method9_in1 ),
   .RDY_method10( RDY_method10 ),
   .method10( { method10_0_a,method10_0_b,method10_0_c,method10_1_a,method10_1_b,method10_1_c,method10_2_a,method10_2_b,method10_2_c } ),
   .RDY_method20( RDY_method20 ),
   .method20( method20 )
  );

endmodule

