function Integer a(Integer in);
  return (in+1);
endfunction

function Integer b(Integer in);
  return (in+2);
endfunction

typedef function Integer f(Integer in) FuncType;
FuncType funcs[2] = {a, b};

(* synthesize *)
module mkArrayCurry();

  Reg#(Bit#(1)) switch <- mkReg(0);

  Integer test = funcs[switch](5);
  
  rule go;
    $display(test);
    $finish(0);
  endrule

endmodule
