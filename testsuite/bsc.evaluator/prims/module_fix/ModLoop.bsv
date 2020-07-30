// test the infinite-loop error with PrimModuleFix

interface Test;
  method Action test;
endinterface

module mkTest#(Test ifc)(Test);
  return(ifc);
endmodule

(* synthesize *)
module sysModLoop();

  Test test <- moduleFix(mkTest);

  rule go;
    test.test;
    $finish(0);
  endrule

endmodule

