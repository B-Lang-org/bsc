function ActionValue#(Bool) avf(Reg#(Bool) r);
  actionvalue
    return r._read();
  endactionvalue
endfunction
