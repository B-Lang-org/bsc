function Integer a(Integer in);
  return (in+1);
endfunction

function Integer b(Integer in);
  return (in+2);
endfunction

(* options="-aggressive-conditions" *)
(* synthesize *)
module mkWhenCurry();

  Reg#(Bool) switch <- mkReg(False);
  Reg#(Bool) pred1 <- mkReg(True);
  Reg#(Bool) pred2 <- mkReg(True);

  Integer test = (switch ? when(pred1, a) : when(pred2, b))(5);
  
  rule go;
    $display(test);
    $finish(0);
  endrule

endmodule
