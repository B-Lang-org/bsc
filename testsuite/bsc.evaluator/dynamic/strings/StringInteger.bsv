(* synthesize *)
module sysStringInteger();

  Reg#(Bit#(2)) c <- mkReg(0);

  String x = (c[0] == 1) ? "This is a test string" : 
                           "This is a string with 35 characters";

  String y = (c[0] == 1) ? "This has \003 \007 \011 unprintable characters" : 
                           "This \n has \n newlines\nin it";

  String z = (c[1] == 1) ? x : y;

  rule test;
    $display("Length: %0d", stringLength(z));
    $display("%h", z);
    $display("%h", Bit#(400)'(fromInteger(primStringToInteger(z))));
    c <= c + 1;
    if(c == 3) $finish(0);
  endrule

endmodule
