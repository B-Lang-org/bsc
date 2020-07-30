// A noinline function of no arguments might be used to compute a
// complicated constant value, such as a lookup table.

(* noinline *)
function Bit#(8) fnNoInline_NoArgs();
   return 8'b10101010;
endfunction

(* synthesize *)
module sysNoInline_NoArgs ();
   Reg#(Bool) done <- mkReg(False);

   rule display (!done);
      $display("%b", fnNoInline_NoArgs);
      done <= True;
   endrule

   rule finish (done);
      $finish(0);
   endrule

endmodule

