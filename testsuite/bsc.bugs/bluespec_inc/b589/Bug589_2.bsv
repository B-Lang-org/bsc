function Action foo(Bool y, Reg#(Bool) r);
  action
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
    x = !x;
  endaction
  endaction
endfunction: foo
