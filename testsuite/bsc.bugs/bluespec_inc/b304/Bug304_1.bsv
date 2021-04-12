
function Bool f ();
  case (tuple2(True,False)) matches
      {.i,.i} : f = i;
      default: f = True;
  endcase
endfunction

