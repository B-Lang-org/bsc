(* synthesize *)
module sysLog2TestM();

  Bool pass = True;
  Integer power = 1;
  for(Integer i = 0; primSeq(pass,primSeq(power,i <= 65536)); i = i + 1)
    begin
      if(log2(power) != i) begin
        pass = False;
        addRules(
        rules
        rule fail_1; 
          $display("Fail %0d", i);
        endrule
        endrules);
      end
      if(i > 2 && log2(power - 1) != i) begin
        pass = False;
        addRules(
        rules
        rule fail2;
        $display("Fail -1 %0d", i);
        endrule
        endrules);
      end
      if(log2(power + 1) != i + 1) begin
        pass = False;
        addRules(
        rules
        rule fail3;
           $display("Fail +1 %0d", i);
        endrule
        endrules);
      end
      messageM(integerToString(i));
      power = power * 2;
    end

    rule show_pass(pass);
	 $display("Test passed");
    endrule
   
    rule exit;
      $finish(0);
    endrule
      
endmodule
