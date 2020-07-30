// autocreated by expandPorts.tcl 2.0 and portUtil.tcl 2.0
module mkTest11_expanded (
    CLK,
    RST_N,
    RDY_add,
    EN_add,
    add_s_a,
    add_s_b,
    RDY_sum,
    sum_sum,
    sum_cry,
    RDY_tst,
    tst,
    tst_z );

  input CLK;
  input RST_N;

  // ====================
  // Method = add
  //   ready  => RDY_add                1   Bit#(1)
  //   enable => EN_add                 1   Bit#(1)
  //   input  => add_s                 64   Test11::TS
  output  RDY_add;
  input  EN_add;
  input  [ 31 : 0 ] add_s_a;
  input  [ 31 : 0 ] add_s_b;

  // ====================
  // Method = sum
  //   ready  => RDY_sum                1   Bit#(1)
  //   result => sum                   33   Test11::TSum
  output  RDY_sum;
  output  [ 31 : 0 ] sum_sum;  // sum[32:1]
  output  sum_cry;  // sum[0:0]

  // ====================
  // Method = tst
  //   ready  => RDY_tst                1   Bit#(1)
  //   result => tst                    2   {Tuple2#(Bit#(1), Bit#(1))}
  //   input  => tst_z                  3   {Tuple3#(Bit#(1), Bit#(1), Bit#(1))}
  output  RDY_tst;
  output  [ 1 : 0 ] tst;
  input  [ 2 : 0 ] tst_z;


  wire   RDY_add;
  wire   RDY_sum;
  wire   [ 31 : 0 ] sum_sum;  // sum[32:1]
  wire   sum_cry;  // sum[0:0]
  wire   RDY_tst;
  wire   [ 1 : 0 ] tst;

  mkTest11 _mkTest11 ( 
   .CLK( CLK ),
   .RST_N( RST_N ),
   .RDY_add( RDY_add ),
   .EN_add( EN_add ),
   .add_s( { add_s_a,add_s_b } ),
   .RDY_sum( RDY_sum ),
   .sum( { sum_sum,sum_cry } ),
   .RDY_tst( RDY_tst ),
   .tst( tst ),
   .tst_z( tst_z )
  );

endmodule

