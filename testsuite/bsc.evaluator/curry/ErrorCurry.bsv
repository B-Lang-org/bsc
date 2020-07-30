function Integer a(Integer in);
  return (in+1);
endfunction

function Integer b(Integer in);
  return (in+2);
endfunction

(* synthesize *)
module mkErrorCurry();

  Reg#(Bool) switch <- mkReg(False);

  Integer test = (switch ? error("a") : b)(5);
  
  rule go;
    $display(test);
    $finish(0);
  endrule

endmodule
