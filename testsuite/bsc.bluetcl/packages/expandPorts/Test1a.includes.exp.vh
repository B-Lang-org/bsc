// autocreated by expandPorts.tcl 2.0 and portUtil.tcl 2.0

  wire   CLK;
  wire   RST_N;
  // ====================
  // Method = method2
  //   ready  => amIready               1   Bit#(1)
  //   result => method2               12   Test1a::TS
  //   input  => method2_in1           32   Int#(32)
  //   input  => method2_in2           32   Int#(32)
  wire   amIready;
  wire   [ 11 : 0 ] method2;
  wire   [ 3 : 0 ] method2_a;  // method2[11:8]
  wire   [ 3 : 0 ] method2_b;  // method2[7:4]
  wire   [ 3 : 0 ] method2_c;  // method2[3:0]
  wire   [ 31 : 0 ] method2_in1;
  wire   [ 31 : 0 ] method2_in2;

  // ====================
  // Method = method3
  //   enable => EN_method3             1   Bit#(1)
  //   input  => method3_in1           32   Int#(32)
  //   input  => method3_in2           12   Test1a::TS
  wire   EN_method3;
  wire   [ 31 : 0 ] method3_in1;
  wire   [ 11 : 0 ] method3_in2;
  wire   [ 3 : 0 ] method3_in2_a;
  wire   [ 3 : 0 ] method3_in2_b;
  wire   [ 3 : 0 ] method3_in2_c;

  // ====================
  // Method = method4
  //   result => method4               32   Int#(32)
  wire   [ 31 : 0 ] method4;


`ifndef __EXPANDPORTS_NO_RENAMES__
  assign method2_a = method2[11:8];
  assign method2_b = method2[7:4];
  assign method2_c = method2[3:0];
  assign method3_in2[11:8] = method3_in2_a;
  assign method3_in2[7:4] = method3_in2_b;
  assign method3_in2[3:0] = method3_in2_c;
`endif

`ifndef __EXPANDPORTS_DONT_CREATE_DUT__
  mkTest1a _mkTest1a ( 
   .CLK( CLK ),
   .RST_N( RST_N ),
   .amIready( amIready ),
   .method2( method2 ),
   .method2_in1( method2_in1 ),
   .method2_in2( method2_in2 ),
   .EN_method3( EN_method3 ),
   .method3_in1( method3_in1 ),
   .method3_in2( method3_in2 ),
   .method4( method4 )
  );
`endif
