// autocreated by expandPorts.tcl 2.0 and portUtil.tcl 2.0
module mkTest1a_expanded (
    CLK,
    RST_N,
    amIready,
    method2_a,
    method2_b,
    method2_c,
    method2_in1,
    method2_in2,
    EN_method3,
    method3_in1,
    method3_in2_a,
    method3_in2_b,
    method3_in2_c,
    method4 );

  input CLK;
  input RST_N;

  // ====================
  // Method = method2
  //   ready  => amIready               1   Bit#(1)
  //   result => method2               12   Test1a::TS
  //   input  => method2_in1           32   Int#(32)
  //   input  => method2_in2           32   Int#(32)
  output  amIready;
  output  [ 3 : 0 ] method2_a;  // method2[11:8]
  output  [ 3 : 0 ] method2_b;  // method2[7:4]
  output  [ 3 : 0 ] method2_c;  // method2[3:0]
  input  [ 31 : 0 ] method2_in1;
  input  [ 31 : 0 ] method2_in2;

  // ====================
  // Method = method3
  //   enable => EN_method3             1   Bit#(1)
  //   input  => method3_in1           32   Int#(32)
  //   input  => method3_in2           12   Test1a::TS
  input  EN_method3;
  input  [ 31 : 0 ] method3_in1;
  input  [ 3 : 0 ] method3_in2_a;
  input  [ 3 : 0 ] method3_in2_b;
  input  [ 3 : 0 ] method3_in2_c;

  // ====================
  // Method = method4
  //   result => method4               32   Int#(32)
  output  [ 31 : 0 ] method4;


  wire   amIready;
  wire   [ 3 : 0 ] method2_a;  // method2[11:8]
  wire   [ 3 : 0 ] method2_b;  // method2[7:4]
  wire   [ 3 : 0 ] method2_c;  // method2[3:0]
  wire   [ 31 : 0 ] method4;

  mkTest1a _mkTest1a ( 
   .CLK( CLK ),
   .RST_N( RST_N ),
   .amIready( amIready ),
   .method2( { method2_a,method2_b,method2_c } ),
   .method2_in1( method2_in1 ),
   .method2_in2( method2_in2 ),
   .EN_method3( EN_method3 ),
   .method3_in1( method3_in1 ),
   .method3_in2( { method3_in2_a,method3_in2_b,method3_in2_c } ),
   .method4( method4 )
  );

endmodule

