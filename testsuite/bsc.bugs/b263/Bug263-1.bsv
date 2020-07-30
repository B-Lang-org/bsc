function Action status (Bool a);
action
  if (a)
    $display ("True");
  else
    $display ("False");
endaction 
endfunction : status
