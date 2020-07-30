import DeprecatedLibraryBSV::*;

Bool y = myFn(False);

module mkTest();
   Empty i1 <- mkFoo;
   Reg#(Bool) i2 <- mkImp;
endmodule

