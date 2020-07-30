// autocreated by expandPorts.tcl 2.0 and portUtil.tcl 2.0

  wire   CLK;
  wire   RST_N;
  // ====================
  // Method = add
  //   ready  => RDY_add                1   Bit#(1)
  //   enable => EN_add                 1   Bit#(1)
  //   input  => add_s                 64   Test11::TS
  wire   RDY_add;
  wire   EN_add;
  wire   [ 63 : 0 ] add_s;
  wire   [ 31 : 0 ] add_s_a;
  wire   [ 31 : 0 ] add_s_b;

  // ====================
  // Method = sum
  //   ready  => RDY_sum                1   Bit#(1)
  //   result => sum                   33   Test11::TSum
  wire   RDY_sum;
  wire   [ 32 : 0 ] sum;
  wire   [ 31 : 0 ] sum_sum;  // sum[32:1]
  wire   sum_cry;  // sum[0:0]

  // ====================
  // Method = tst
  //   ready  => RDY_tst                1   Bit#(1)
  //   result => tst                    2   {Tuple2#(Bit#(1), Bit#(1))}
  //   input  => tst_z                  3   {Tuple3#(Bit#(1), Bit#(1), Bit#(1))}
  wire   RDY_tst;
  wire   [ 1 : 0 ] tst;
  wire   [ 2 : 0 ] tst_z;


`ifndef __EXPANDPORTS_NO_RENAMES__
  assign add_s[63:32] = add_s_a;
  assign add_s[31:0] = add_s_b;
  assign sum_sum = sum[32:1];
  assign sum_cry = sum[0:0];
`endif

`ifndef __EXPANDPORTS_DONT_CREATE_DUT__
  mkTest11 _mkTest11 ( 
   .CLK( CLK ),
   .RST_N( RST_N ),
   .RDY_add( RDY_add ),
   .EN_add( EN_add ),
   .add_s( add_s ),
   .RDY_sum( RDY_sum ),
   .sum( sum ),
   .RDY_tst( RDY_tst ),
   .tst( tst ),
   .tst_z( tst_z )
  );
`endif
