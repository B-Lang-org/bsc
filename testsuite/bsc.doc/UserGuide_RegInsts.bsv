typedef UInt#(51) NumTyp;

(* synthesize *)
module sysUserGuide_RegInsts();

  Reg #(NumTyp) x(); // x is the interface to the register
  mkReg#(0) reg_1(x);    // reg_1 is the register instance

  Reg #(NumTyp) y();
  mkRegU reg_2(y);

  Reg #(NumTyp) z();
  mkRegA#(0) reg_3(z);

endmodule

