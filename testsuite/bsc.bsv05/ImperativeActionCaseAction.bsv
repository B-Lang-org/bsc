function Action foo(Bool y, Reg#(Bool) r);
  action
    Bool x;
    case (y)
      True: action
              x = !y;
              r <= x;
            endaction
      False: action
               x = y;
               r <= x;
             endaction
    endcase
  endaction
endfunction: foo

module bar();
  Reg #(Bool) r();
  mkReg#(False) r_inst(r);

  rule bogus;
    foo(r, r);
  endrule
endmodule: bar
