// This should not compile because
// the parameter name is repeated
interface Test #(parameter type a);
    method Action setInput(a x, a y);
    method a getOutput();
endinterface: Test

module mkTest(Test#(Bool));
    method Action setInput(Bool x, Bool x);
      action endaction
    endmethod
    method Bool getOutput();
      getOutput = False;
    endmethod
endmodule
