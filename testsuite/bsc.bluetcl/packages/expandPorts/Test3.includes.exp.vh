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
  //   input  => method6_in1           12   Test3::TS
  wire   RDY_method6;
  wire   [ 31 : 0 ] method6;
  wire   [ 11 : 0 ] method6_in1;
  wire   [ 3 : 0 ] method6_in1_a;
  wire   [ 3 : 0 ] method6_in1_b;
  wire   [ 3 : 0 ] method6_in1_c;

  // ====================
  // Method = method7
  //   ready  => RDY_method7            1   Bit#(1)
  //   result => method7               36   {Vector::Vector#(3, Test3::TS)}
  wire   RDY_method7;
  wire   [ 35 : 0 ] method7;
  wire   [ 3 : 0 ] method7_0_a;  // method7[35:32]
  wire   [ 3 : 0 ] method7_0_b;  // method7[31:28]
  wire   [ 3 : 0 ] method7_0_c;  // method7[27:24]
  wire   [ 3 : 0 ] method7_1_a;  // method7[23:20]
  wire   [ 3 : 0 ] method7_1_b;  // method7[19:16]
  wire   [ 3 : 0 ] method7_1_c;  // method7[15:12]
  wire   [ 3 : 0 ] method7_2_a;  // method7[11:8]
  wire   [ 3 : 0 ] method7_2_b;  // method7[7:4]
  wire   [ 3 : 0 ] method7_2_c;  // method7[3:0]

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
  //   result => method10             144   {Vector::Vector#(3, Vector::Vector#(4, Test3::TS))}
  wire   RDY_method10;
  wire   [ 143 : 0 ] method10;
  wire   [ 3 : 0 ] method10_0_0_a;  // method10[143:140]
  wire   [ 3 : 0 ] method10_0_0_b;  // method10[139:136]
  wire   [ 3 : 0 ] method10_0_0_c;  // method10[135:132]
  wire   [ 3 : 0 ] method10_0_1_a;  // method10[131:128]
  wire   [ 3 : 0 ] method10_0_1_b;  // method10[127:124]
  wire   [ 3 : 0 ] method10_0_1_c;  // method10[123:120]
  wire   [ 3 : 0 ] method10_0_2_a;  // method10[119:116]
  wire   [ 3 : 0 ] method10_0_2_b;  // method10[115:112]
  wire   [ 3 : 0 ] method10_0_2_c;  // method10[111:108]
  wire   [ 3 : 0 ] method10_0_3_a;  // method10[107:104]
  wire   [ 3 : 0 ] method10_0_3_b;  // method10[103:100]
  wire   [ 3 : 0 ] method10_0_3_c;  // method10[99:96]
  wire   [ 3 : 0 ] method10_1_0_a;  // method10[95:92]
  wire   [ 3 : 0 ] method10_1_0_b;  // method10[91:88]
  wire   [ 3 : 0 ] method10_1_0_c;  // method10[87:84]
  wire   [ 3 : 0 ] method10_1_1_a;  // method10[83:80]
  wire   [ 3 : 0 ] method10_1_1_b;  // method10[79:76]
  wire   [ 3 : 0 ] method10_1_1_c;  // method10[75:72]
  wire   [ 3 : 0 ] method10_1_2_a;  // method10[71:68]
  wire   [ 3 : 0 ] method10_1_2_b;  // method10[67:64]
  wire   [ 3 : 0 ] method10_1_2_c;  // method10[63:60]
  wire   [ 3 : 0 ] method10_1_3_a;  // method10[59:56]
  wire   [ 3 : 0 ] method10_1_3_b;  // method10[55:52]
  wire   [ 3 : 0 ] method10_1_3_c;  // method10[51:48]
  wire   [ 3 : 0 ] method10_2_0_a;  // method10[47:44]
  wire   [ 3 : 0 ] method10_2_0_b;  // method10[43:40]
  wire   [ 3 : 0 ] method10_2_0_c;  // method10[39:36]
  wire   [ 3 : 0 ] method10_2_1_a;  // method10[35:32]
  wire   [ 3 : 0 ] method10_2_1_b;  // method10[31:28]
  wire   [ 3 : 0 ] method10_2_1_c;  // method10[27:24]
  wire   [ 3 : 0 ] method10_2_2_a;  // method10[23:20]
  wire   [ 3 : 0 ] method10_2_2_b;  // method10[19:16]
  wire   [ 3 : 0 ] method10_2_2_c;  // method10[15:12]
  wire   [ 3 : 0 ] method10_2_3_a;  // method10[11:8]
  wire   [ 3 : 0 ] method10_2_3_b;  // method10[7:4]
  wire   [ 3 : 0 ] method10_2_3_c;  // method10[3:0]


`ifndef __EXPANDPORTS_NO_RENAMES__
  assign method6_in1[11:8] = method6_in1_a;
  assign method6_in1[7:4] = method6_in1_b;
  assign method6_in1[3:0] = method6_in1_c;
  assign method7_0_a = method7[35:32];
  assign method7_0_b = method7[31:28];
  assign method7_0_c = method7[27:24];
  assign method7_1_a = method7[23:20];
  assign method7_1_b = method7[19:16];
  assign method7_1_c = method7[15:12];
  assign method7_2_a = method7[11:8];
  assign method7_2_b = method7[7:4];
  assign method7_2_c = method7[3:0];
  assign method10_0_0_a = method10[143:140];
  assign method10_0_0_b = method10[139:136];
  assign method10_0_0_c = method10[135:132];
  assign method10_0_1_a = method10[131:128];
  assign method10_0_1_b = method10[127:124];
  assign method10_0_1_c = method10[123:120];
  assign method10_0_2_a = method10[119:116];
  assign method10_0_2_b = method10[115:112];
  assign method10_0_2_c = method10[111:108];
  assign method10_0_3_a = method10[107:104];
  assign method10_0_3_b = method10[103:100];
  assign method10_0_3_c = method10[99:96];
  assign method10_1_0_a = method10[95:92];
  assign method10_1_0_b = method10[91:88];
  assign method10_1_0_c = method10[87:84];
  assign method10_1_1_a = method10[83:80];
  assign method10_1_1_b = method10[79:76];
  assign method10_1_1_c = method10[75:72];
  assign method10_1_2_a = method10[71:68];
  assign method10_1_2_b = method10[67:64];
  assign method10_1_2_c = method10[63:60];
  assign method10_1_3_a = method10[59:56];
  assign method10_1_3_b = method10[55:52];
  assign method10_1_3_c = method10[51:48];
  assign method10_2_0_a = method10[47:44];
  assign method10_2_0_b = method10[43:40];
  assign method10_2_0_c = method10[39:36];
  assign method10_2_1_a = method10[35:32];
  assign method10_2_1_b = method10[31:28];
  assign method10_2_1_c = method10[27:24];
  assign method10_2_2_a = method10[23:20];
  assign method10_2_2_b = method10[19:16];
  assign method10_2_2_c = method10[15:12];
  assign method10_2_3_a = method10[11:8];
  assign method10_2_3_b = method10[7:4];
  assign method10_2_3_c = method10[3:0];
`endif

`ifndef __EXPANDPORTS_DONT_CREATE_DUT__
  mkTest3 _mkTest3 ( 
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
   .method10( method10 )
  );
`endif
