ActionValue#(Bool) av;
av =
  actionvalue
    function bit[0:0] id(bit[0:0] x);
      return x;
    endfunction
    return True;
  endactionvalue;
