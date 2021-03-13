function String showBool(Bool b);
   return(b ? "True" : "False");
endfunction

typedef struct {
  a field;
} T;

(* synthesize *)
module sysPolyFieldCond();
  Reg #(Bool) cond <- mkReg(False);
  T x = T { field: when (cond, ?) };
  Bool b = impCondOf (x);
  rule r;
    $display("Cond: ", showBool(b));
    $finish(0);
  endrule
endmodule

