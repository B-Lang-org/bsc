// This should not compile because
// the parameter name is repeated
interface Test #(parameter type a);
    method Action setInput(a x, a x);
    method a getOutput();
endinterface: Test
