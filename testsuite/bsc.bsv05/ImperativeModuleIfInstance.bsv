module mkFoo#(parameter Bool cond)(Reg#(Bool));
  // XXX one should be able to declare the variable outside of the if;
  // XXX this is an ugly hack
  if (cond)
   begin     
      Reg#(Bool) r();
      mkReg#(True) the_r(r);
      return (asReg(r));
   end
  else
   begin
    Reg#(Bool) r();
    mkRegU the_r(r);
      return (asReg(r));
   end
endmodule
