
interface Test;
  method Bit#(32) test();
endinterface: Test

module sysMethodNeverReady(Test);
  method test() if (False);
    return (0);
  endmethod: test
endmodule: sysMethodNeverReady

