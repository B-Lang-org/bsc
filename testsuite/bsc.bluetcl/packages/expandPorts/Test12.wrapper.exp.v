// autocreated by expandPorts.tcl 2.0 and portUtil.tcl 2.0
module mkTest12_expanded (
    CLK,
    RST_N,
    EN_add,
    add_a );

  input CLK;
  input RST_N;

  // ====================
  // Method = add
  //   enable => EN_add                 1   Bit#(1)
  //   input  => add_a                 32   Int#(32)
  input  EN_add;
  input  [ 31 : 0 ] add_a;

  // ====================
  // Method = advance




  mkTest12 _mkTest12 ( 
   .CLK( CLK ),
   .RST_N( RST_N ),
   .EN_add( EN_add ),
   .add_a( add_a )
  );

endmodule

