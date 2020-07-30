// This should not compile because 
// the method name is repeated 
interface Test #(parameter type a);
    method Action setInput(a x, a y);
    method Action setInput(a x, a y);
    method a getOutput();
endinterface: Test
