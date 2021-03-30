ActionValue#(Bool) av;
av =
  actionvalue
    bit[3:0] x;
    x <- actionvalue return(3); endactionvalue;
    return True;
  endactionvalue;
