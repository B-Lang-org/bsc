(* noinline *)
function Action fnNoInline_ResAction (Bit#(8) x);
   action
      $display(x);
   endaction
endfunction

