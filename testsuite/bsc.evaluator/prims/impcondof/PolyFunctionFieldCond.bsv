function String showBool(Bool b);
   return(b ? "True" : "False");
endfunction

typedef struct {
  function b f(a x) field;
} T;

(* synthesize *)
module sysPolyFunctionFieldCond();
  Reg #(Bool) cond <- mkReg(False);
  T x = T { field: when (cond, ?) };
  Bool b = impCondOf (x);
  rule r;
    $display("Cond: ", showBool(b));
    $finish(0);
  endrule
endmodule
