(* synthesize *)
module sysDynamicFormatString();

  Reg#(Bit#(2)) c <- mkReg(0);

  String x = (c[0] == 1) ? "%h" : "%s"; 

  String y = (c[1] == 1) ? "%h" : "%s"; 
   
  String fmt_string = strConcat(x,strConcat(" ",y));
   
  rule test;
    $display(fmt_string, "Hello", "World");
    c <= c + 1;
    if(c == 3) $finish(0);
  endrule

endmodule
