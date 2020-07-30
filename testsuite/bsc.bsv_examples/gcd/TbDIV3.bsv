import DIV3::*;

(* synthesize *)
module mkTbDIV3(Empty);

  Divisible_IFC div3 <- mkDIV3();
  Reg#(Int#(32)) counter <- mkReg(7);

  rule rule1_sendInput (True);
    (div3.nextDigit)(counter);
    counter <= counter + 1;
  endrule: rule1_sendInput

  rule rule2_getResult (True);
    if (div3.isDivisible())
      $display("%d is divisible by 3", counter - 1);
    else
      $display("%d is NOT divisible by 3", counter - 1);
  endrule: rule2_getResult

  rule done (counter >= 15);
    $finish(0);
  endrule: done

endmodule: mkTbDIV3

