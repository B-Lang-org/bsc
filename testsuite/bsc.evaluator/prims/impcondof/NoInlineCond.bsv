(* noinline *)
function UInt#(32) inc(UInt#(32) i);
   return(i + 1);
endfunction

function String showBool(Bool b);
   return(b ? "True" : "False");
endfunction

(* synthesize *)
module sysNoInlineCond();
   rule test;
      $display("Cond: ", showBool(impCondOf(inc)));
      $finish(0);
   endrule
endmodule

