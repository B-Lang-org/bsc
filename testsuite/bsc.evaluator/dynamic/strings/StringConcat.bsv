(* synthesize *)
module sysStringConcat();

  Reg#(Bit#(4)) c <- mkReg(0);

  String x = (c[0] == 1) ? "AAA" : "B";
  String y = (c[1] == 1) ? "CCCC" : "DD";
  String z = strConcat(x,y);

  String r = (c[2] == 1) ? "RRRR" : "RR";
  String s = (c[3] == 1) ? "SSSSS" : "SS";

  String t = strConcat(r, s);
  
  String o = strConcat(z,t);

  rule test;
    $display(o);
    $display("Length is %0d", stringLength(o));
    c <= c + 1;
    if(c == 15) $finish(0);
  endrule

endmodule
