(* synthesize *)
module sysStringEQ();

  Reg#(Bit#(4)) c <- mkReg(0);

  String x = (c[0] == 1) ? "AAA" : "B";
  String y = (c[1] == 1) ? "CCCC" : "";
  String z = strConcat(x,y);

  String r = (c[2] == 1) ? "" : "RR";
  String s = (c[3] == 1) ? "SSSSS" : "SS";

  String t = strConcat(r,s);
  
  String o = strConcat(z,t);

  rule test;
    $display("Test %b", c);
    if (z == x) $display("z equals x");
    else $display ("z does not equal x");

    if (o == strConcat(x,s))
      $display("y and r are empty");

    if (o == "AAACCCCRRSS") 
      $display("o is AAACCCCRRSS");
    
    $display("o: %s", o);
    $display;
    c <= c + 1;
    if(c == 15) $finish(0);
  endrule

endmodule
