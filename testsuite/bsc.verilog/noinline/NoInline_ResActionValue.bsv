(* noinline *)
function ActionValue#(Bit#(8)) fnNoInline_ResActionValue (Bit#(8) x);
   actionvalue
      $display(x);
      return (x + 1);
   endactionvalue
endfunction

