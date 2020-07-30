(* noinline *)
function Bit#(8) fnNoInline(Bit#(8) x);
   return (x + 1);
endfunction

(* synthesize *)
module sysNoInline ();
  rule r;
     $display(fnNoInline(0) + 8);
  endrule

endmodule

