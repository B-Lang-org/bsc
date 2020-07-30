// autocreated by expandPorts.tcl 2.0 and portUtil.tcl 2.0

  wire   CLK;
  wire   RST_N;
  // ====================
  // Method = add
  //   enable => EN_add                 1   Bit#(1)
  //   input  => add_a                 32   Int#(32)
  wire   EN_add;
  wire   [ 31 : 0 ] add_a;

  // ====================
  // Method = advance


`ifndef __EXPANDPORTS_NO_RENAMES__
`endif

`ifndef __EXPANDPORTS_DONT_CREATE_DUT__
  mkTest12 _mkTest12 ( 
   .CLK( CLK ),
   .RST_N( RST_N ),
   .EN_add( EN_add ),
   .add_a( add_a )
  );
`endif
