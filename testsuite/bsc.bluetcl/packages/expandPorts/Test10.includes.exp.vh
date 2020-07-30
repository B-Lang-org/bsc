// autocreated by expandPorts.tcl 2.0 and portUtil.tcl 2.0

  wire   CLK;
  wire   RST_N;
  // ====================
  // Method = add
  //   ready  => RDY_add                1   Bit#(1)
  //   enable => EN_add                 1   Bit#(1)
  //   input  => add_s                 64   Test10::TS
  wire   RDY_add;
  wire   EN_add;
  wire   [ 63 : 0 ] add_s;
  wire   [ 31 : 0 ] add_s_a;
  wire   [ 31 : 0 ] add_s_b;

  // ====================
  // Method = sum
  //   ready  => RDY_sum                1   Bit#(1)
  //   result => sum                   32   Int#(32)
  wire   RDY_sum;
  wire   [ 31 : 0 ] sum;


`ifndef __EXPANDPORTS_NO_RENAMES__
  assign add_s[63:32] = add_s_a;
  assign add_s[31:0] = add_s_b;
`endif

`ifndef __EXPANDPORTS_DONT_CREATE_DUT__
  mkTest10 _mkTest10 ( 
   .CLK( CLK ),
   .RST_N( RST_N ),
   .RDY_add( RDY_add ),
   .EN_add( EN_add ),
   .add_s( add_s ),
   .RDY_sum( RDY_sum ),
   .sum( sum )
  );
`endif
