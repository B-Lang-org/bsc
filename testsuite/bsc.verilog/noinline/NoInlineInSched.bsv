(* noinline *)
function Bool inv (Bool x);
   return !x;
endfunction

(* synthesize *)
module sysNoInlineInSched ();
   Reg#(Bool) b <- mkReg(False);

   rule r1 (inv(b));
      $display("Rule fired");
      b <= True;
   endrule

   rule r2 (b);
      $finish(0);
   endrule
endmodule

