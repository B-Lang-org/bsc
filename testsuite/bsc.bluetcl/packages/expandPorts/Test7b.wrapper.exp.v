// autocreated by expandPorts.tcl 2.0 and portUtil.tcl 2.0
module mkTest7b_expanded (
    system_clock_1,
    funky_input,
    system_clock,
    reset_n,
    I0_M1_ready,
    I0_M1_enable,
    I0_M1_in1,
    I0_M1_in2,
    I0_M2_ready,
    I0_M2_output,
    I0_M2_in1,
    I0_M2_in2,
    I1_M1_ready,
    I1_M1_enable,
    I1_M1_in1,
    I1_M1_in2,
    I1_M2_ready,
    I1_M2_output,
    I1_M2_in1,
    I1_M2_in2 );

  input system_clock_1;
  input  [ 3 : 0 ] funky_input;
  input system_clock;
  input reset_n;

  // ====================
  // Method = ifcA_0_method1
  //   ready  => RDY_ifcA_0_method1     1   Bit#(1)
  //   enable => EN_ifcA_0_method1      1   Bit#(1)
  //   input  => ifcA_0_method1_in1    32   Int#(32)
  //   input  => ifcA_0_method1_in2    32   Int#(32)
  output  I0_M1_ready;  // RDY_ifcA_0_method1[0:0]
  input  I0_M1_enable;
  input  [ 31 : 0 ] I0_M1_in1;
  input  [ 31 : 0 ] I0_M1_in2;

  // ====================
  // Method = ifcA_0_method2
  //   ready  => RDY_ifcA_0_method2     1   Bit#(1)
  //   result => ifcA_0_method2        32   Int#(32)
  //   input  => ifcA_0_method2_in1    32   Int#(32)
  //   input  => ifcA_0_method2_in2    32   Int#(32)
  output  I0_M2_ready;  // RDY_ifcA_0_method2[0:0]
  output  [ 31 : 0 ] I0_M2_output;  // ifcA_0_method2[31:0]
  input  [ 31 : 0 ] I0_M2_in1;
  input  [ 31 : 0 ] I0_M2_in2;

  // ====================
  // Method = ifcA_1_method1
  //   ready  => RDY_ifcA_1_method1     1   Bit#(1)
  //   enable => EN_ifcA_1_method1      1   Bit#(1)
  //   input  => ifcA_1_method1_in1    32   Int#(32)
  //   input  => ifcA_1_method1_in2    32   Int#(32)
  output  I1_M1_ready;  // RDY_ifcA_1_method1[0:0]
  input  I1_M1_enable;
  input  [ 31 : 0 ] I1_M1_in1;
  input  [ 31 : 0 ] I1_M1_in2;

  // ====================
  // Method = ifcA_1_method2
  //   ready  => RDY_ifcA_1_method2     1   Bit#(1)
  //   result => ifcA_1_method2        32   Int#(32)
  //   input  => ifcA_1_method2_in1    32   Int#(32)
  //   input  => ifcA_1_method2_in2    32   Int#(32)
  output  I1_M2_ready;  // RDY_ifcA_1_method2[0:0]
  output  [ 31 : 0 ] I1_M2_output;  // ifcA_1_method2[31:0]
  input  [ 31 : 0 ] I1_M2_in1;
  input  [ 31 : 0 ] I1_M2_in2;


  wire   I0_M1_ready;  // RDY_ifcA_0_method1[0:0]
  wire   I0_M2_ready;  // RDY_ifcA_0_method2[0:0]
  wire   [ 31 : 0 ] I0_M2_output;  // ifcA_0_method2[31:0]
  wire   I1_M1_ready;  // RDY_ifcA_1_method1[0:0]
  wire   I1_M2_ready;  // RDY_ifcA_1_method2[0:0]
  wire   [ 31 : 0 ] I1_M2_output;  // ifcA_1_method2[31:0]

  mkTest7b _mkTest7b ( 
   .CLK_c1( system_clock_1 ),
   .pIn( funky_input ),
   .CLK( system_clock ),
   .RST_N( reset_n ),
   .RDY_ifcA_0_method1( I0_M1_ready ),
   .EN_ifcA_0_method1( I0_M1_enable ),
   .ifcA_0_method1_in1( I0_M1_in1 ),
   .ifcA_0_method1_in2( I0_M1_in2 ),
   .RDY_ifcA_0_method2( I0_M2_ready ),
   .ifcA_0_method2( I0_M2_output ),
   .ifcA_0_method2_in1( I0_M2_in1 ),
   .ifcA_0_method2_in2( I0_M2_in2 ),
   .RDY_ifcA_1_method1( I1_M1_ready ),
   .EN_ifcA_1_method1( I1_M1_enable ),
   .ifcA_1_method1_in1( I1_M1_in1 ),
   .ifcA_1_method1_in2( I1_M1_in2 ),
   .RDY_ifcA_1_method2( I1_M2_ready ),
   .ifcA_1_method2( I1_M2_output ),
   .ifcA_1_method2_in1( I1_M2_in1 ),
   .ifcA_1_method2_in2( I1_M2_in2 )
  );

endmodule

