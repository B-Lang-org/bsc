function Action status (Bool a);
action
  Bool x;
  x = True;
  while (True)
    begin
      x = !x;
      $display ("True");
    end
endaction 
endfunction : status
