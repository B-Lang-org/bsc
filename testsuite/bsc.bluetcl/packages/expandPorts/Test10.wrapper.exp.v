// autocreated by expandPorts.tcl 2.0 and portUtil.tcl 2.0
module mkTest10_expanded (
    CLK,
    RST_N,
    RDY_add,
    EN_add,
    add_s_a,
    add_s_b,
    RDY_sum,
    sum );

  input CLK;
  input RST_N;

  // ====================
  // Method = add
  //   ready  => RDY_add                1   Bit#(1)
  //   enable => EN_add                 1   Bit#(1)
  //   input  => add_s                 64   Test10::TS
  output  RDY_add;
  input  EN_add;
  input  [ 31 : 0 ] add_s_a;
  input  [ 31 : 0 ] add_s_b;

  // ====================
  // Method = sum
  //   ready  => RDY_sum                1   Bit#(1)
  //   result => sum                   32   Int#(32)
  output  RDY_sum;
  output  [ 31 : 0 ] sum;


  wire   RDY_add;
  wire   RDY_sum;
  wire   [ 31 : 0 ] sum;

  mkTest10 _mkTest10 ( 
   .CLK( CLK ),
   .RST_N( RST_N ),
   .RDY_add( RDY_add ),
   .EN_add( EN_add ),
   .add_s( { add_s_a,add_s_b } ),
   .RDY_sum( RDY_sum ),
   .sum( sum )
  );

endmodule

