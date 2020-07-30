// autocreated by expandPorts.tcl 2.0 and portUtil.tcl 2.0

  wire   system_clock_1;
  wire   CLK_c1;
  wire   [ 3 : 0 ] funky_input;
  wire   [ 3 : 0 ] pIn;
  wire   system_clock;
  wire   CLK;
  wire   reset_n;
  wire   RST_N;
  // ====================
  // Method = ifcA_0_method1
  //   ready  => RDY_ifcA_0_method1     1   Bit#(1)
  //   enable => EN_ifcA_0_method1      1   Bit#(1)
  //   input  => ifcA_0_method1_in1    32   Int#(32)
  //   input  => ifcA_0_method1_in2    32   Int#(32)
  wire   RDY_ifcA_0_method1;
  wire   I0_M1_ready;  // RDY_ifcA_0_method1[0:0]
  wire   EN_ifcA_0_method1;
  wire   I0_M1_enable;
  wire   [ 31 : 0 ] ifcA_0_method1_in1;
  wire   [ 31 : 0 ] I0_M1_in1;
  wire   [ 31 : 0 ] ifcA_0_method1_in2;
  wire   [ 31 : 0 ] I0_M1_in2;

  // ====================
  // Method = ifcA_0_method2
  //   ready  => RDY_ifcA_0_method2     1   Bit#(1)
  //   result => ifcA_0_method2        32   Int#(32)
  //   input  => ifcA_0_method2_in1    32   Int#(32)
  //   input  => ifcA_0_method2_in2    32   Int#(32)
  wire   RDY_ifcA_0_method2;
  wire   I0_M2_ready;  // RDY_ifcA_0_method2[0:0]
  wire   [ 31 : 0 ] ifcA_0_method2;
  wire   [ 31 : 0 ] I0_M2_output;  // ifcA_0_method2[31:0]
  wire   [ 31 : 0 ] ifcA_0_method2_in1;
  wire   [ 31 : 0 ] I0_M2_in1;
  wire   [ 31 : 0 ] ifcA_0_method2_in2;
  wire   [ 31 : 0 ] I0_M2_in2;

  // ====================
  // Method = ifcA_1_method1
  //   ready  => RDY_ifcA_1_method1     1   Bit#(1)
  //   enable => EN_ifcA_1_method1      1   Bit#(1)
  //   input  => ifcA_1_method1_in1    32   Int#(32)
  //   input  => ifcA_1_method1_in2    32   Int#(32)
  wire   RDY_ifcA_1_method1;
  wire   I1_M1_ready;  // RDY_ifcA_1_method1[0:0]
  wire   EN_ifcA_1_method1;
  wire   I1_M1_enable;
  wire   [ 31 : 0 ] ifcA_1_method1_in1;
  wire   [ 31 : 0 ] I1_M1_in1;
  wire   [ 31 : 0 ] ifcA_1_method1_in2;
  wire   [ 31 : 0 ] I1_M1_in2;

  // ====================
  // Method = ifcA_1_method2
  //   ready  => RDY_ifcA_1_method2     1   Bit#(1)
  //   result => ifcA_1_method2        32   Int#(32)
  //   input  => ifcA_1_method2_in1    32   Int#(32)
  //   input  => ifcA_1_method2_in2    32   Int#(32)
  wire   RDY_ifcA_1_method2;
  wire   I1_M2_ready;  // RDY_ifcA_1_method2[0:0]
  wire   [ 31 : 0 ] ifcA_1_method2;
  wire   [ 31 : 0 ] I1_M2_output;  // ifcA_1_method2[31:0]
  wire   [ 31 : 0 ] ifcA_1_method2_in1;
  wire   [ 31 : 0 ] I1_M2_in1;
  wire   [ 31 : 0 ] ifcA_1_method2_in2;
  wire   [ 31 : 0 ] I1_M2_in2;


`ifndef __EXPANDPORTS_NO_RENAMES__
  assign CLK_c1 = system_clock_1;
  assign pIn = funky_input;
  assign CLK = system_clock;
  assign RST_N = reset_n;
  assign I0_M1_ready = RDY_ifcA_0_method1[0:0];
  assign EN_ifcA_0_method1[0:0] = I0_M1_enable;
  assign ifcA_0_method1_in1[31:0] = I0_M1_in1;
  assign ifcA_0_method1_in2[31:0] = I0_M1_in2;
  assign I0_M2_ready = RDY_ifcA_0_method2[0:0];
  assign I0_M2_output = ifcA_0_method2[31:0];
  assign ifcA_0_method2_in1[31:0] = I0_M2_in1;
  assign ifcA_0_method2_in2[31:0] = I0_M2_in2;
  assign I1_M1_ready = RDY_ifcA_1_method1[0:0];
  assign EN_ifcA_1_method1[0:0] = I1_M1_enable;
  assign ifcA_1_method1_in1[31:0] = I1_M1_in1;
  assign ifcA_1_method1_in2[31:0] = I1_M1_in2;
  assign I1_M2_ready = RDY_ifcA_1_method2[0:0];
  assign I1_M2_output = ifcA_1_method2[31:0];
  assign ifcA_1_method2_in1[31:0] = I1_M2_in1;
  assign ifcA_1_method2_in2[31:0] = I1_M2_in2;
`endif

`ifndef __EXPANDPORTS_DONT_CREATE_DUT__
  mkTest7b _mkTest7b ( 
   .CLK_c1( CLK_c1 ),
   .pIn( funky_input ),
   .CLK( CLK ),
   .RST_N( reset_n ),
   .RDY_ifcA_0_method1( RDY_ifcA_0_method1 ),
   .EN_ifcA_0_method1( EN_ifcA_0_method1 ),
   .ifcA_0_method1_in1( ifcA_0_method1_in1 ),
   .ifcA_0_method1_in2( ifcA_0_method1_in2 ),
   .RDY_ifcA_0_method2( RDY_ifcA_0_method2 ),
   .ifcA_0_method2( ifcA_0_method2 ),
   .ifcA_0_method2_in1( ifcA_0_method2_in1 ),
   .ifcA_0_method2_in2( ifcA_0_method2_in2 ),
   .RDY_ifcA_1_method1( RDY_ifcA_1_method1 ),
   .EN_ifcA_1_method1( EN_ifcA_1_method1 ),
   .ifcA_1_method1_in1( ifcA_1_method1_in1 ),
   .ifcA_1_method1_in2( ifcA_1_method1_in2 ),
   .RDY_ifcA_1_method2( RDY_ifcA_1_method2 ),
   .ifcA_1_method2( ifcA_1_method2 ),
   .ifcA_1_method2_in1( ifcA_1_method2_in1 ),
   .ifcA_1_method2_in2( ifcA_1_method2_in2 )
  );
`endif
