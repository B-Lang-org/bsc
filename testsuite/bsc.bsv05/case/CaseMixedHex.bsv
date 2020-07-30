function String showBool(Bool b);
  return(b ? "True" : "False");
endfunction

function Bool matchHex(Bit#(32) b);
  case (b) matches
    'hd?e?a?d: return (True);
    'h?dead???: return (True);
    'h??dead??: return (True);
    'h????dead: return (True);
    default: return (False);
  endcase
endfunction

Bit#(32) tests[10] = { 32'hd0e0a0d,
                       0,
                       32'hdead1111,
                       32'h11111111,
                       32'h7dead777,
                       32'h77777777,
                       32'h22dead22,
                       32'h22222222,
                       32'hf00ddead,
                       32'hf00df00d };

(* synthesize *)
module sysCaseMixedHex();

  Reg#(UInt#(32)) r <- mkReg(0);
  Reg#(Bit#(32))  b <- mkReg(0);

  rule test;
    $display(showBool(matchHex(b)));
    b <= tests[r];
    if(r == 10) $finish(0);
    r <= r + 1;
  endrule

endmodule

  