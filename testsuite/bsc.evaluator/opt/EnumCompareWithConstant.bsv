typedef enum {
    E0 = 0,
    E1 = 1,
    // E2 = 2,
    E3 = 3,
    E4 = 4
} E deriving (Bits, Eq);


(* synthesize *)
module sysEnumCompareWithConstant();
   Reg#(E) rg <- mkReg(E0);

   rule r (rg == E3);
      $display("E3");
   endrule
endmodule

