function Integer a(Integer in);
  return (in+1);
endfunction

function Integer b(Integer in);
  return (in+2);
endfunction

(* synthesize *)
module mkSeqCurry();
  
  let m1 = message("m1");
  let m2 = message("m2");
  let m3 = message("m3");

  Reg#(Bool) switch <- mkReg(False);

  Integer test = (switch ? primSeq(m2,a) : primSeq(primSeq(m3,m1),b))(5);
  
  rule go;
    $display(test);
    $finish(0);
  endrule

endmodule
