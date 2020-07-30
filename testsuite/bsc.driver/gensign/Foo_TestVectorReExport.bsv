import Bar_VectorReExport::*;

// Test that the import finds Vector::replicateM not List::replicateM

module mkFoo( );

   Vector#( 8, Reg#(Bool) ) cond <- replicateM( mkReg(True) );

endmodule


