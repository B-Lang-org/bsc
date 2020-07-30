(* synthesize *)
module sysLog2Test();

  rule test;
    Bool pass = True;
    Integer power = 1;
    for(Integer i = 0; primSeq(pass, primSeq(power,i <= 65536)); i = i + 1)
    begin
      if(log2(power) != i) begin
        pass = False; 
        $display("Fail %0d", i);
      end
      if(i > 2 && log2(power - 1) != i) begin
        pass = False;
        $display("Fail -1 %0d", i);
      end
      if(log2(power + 1) != i + 1) begin
        pass = False;
        $display("Fail +1 %0d", i);
      end
      messageM(integerToString(i));
      power = power * 2;
    end
    if (pass) $display("Test passed");
    $finish(0);
  endrule

endmodule
