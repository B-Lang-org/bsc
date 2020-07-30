// autocreated by expandPorts.tcl 2.0 and portUtil.tcl 2.0

  wire   CLK;
  wire   RST_N;
  // ====================
  // Method = method3
  //   ready  => RDY_method3            1   Bit#(1)
  //   result => method3               32   Int#(32)
  wire   RDY_method3;
  wire   [ 31 : 0 ] method3;


`ifndef __EXPANDPORTS_NO_RENAMES__
`endif

`ifndef __EXPANDPORTS_DONT_CREATE_DUT__
  mkTest1b _mkTest1b ( 
   .CLK( CLK ),
   .RST_N( RST_N ),
   .RDY_method3( RDY_method3 ),
   .method3( method3 )
  );
`endif
