// autocreated by expandPorts.tcl 2.0 and portUtil.tcl 2.0
module mkTest1b_expanded (
    CLK,
    RST_N,
    RDY_method3,
    method3 );

  input CLK;
  input RST_N;

  // ====================
  // Method = method3
  //   ready  => RDY_method3            1   Bit#(1)
  //   result => method3               32   Int#(32)
  output  RDY_method3;
  output  [ 31 : 0 ] method3;


  wire   RDY_method3;
  wire   [ 31 : 0 ] method3;

  mkTest1b _mkTest1b ( 
   .CLK( CLK ),
   .RST_N( RST_N ),
   .RDY_method3( RDY_method3 ),
   .method3( method3 )
  );

endmodule

