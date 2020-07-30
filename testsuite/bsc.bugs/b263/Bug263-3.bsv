function Action status (Bool a);
action
  Bool x;
  if (a)
    begin
      $display ("True");
      x = True;
    end
  else
    begin
      $display ("False");
      x = False;
    end
endaction 
endfunction : status
