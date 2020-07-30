typedef struct {
  value foo;
  value bar;
} Quux #(parameter type value) deriving(Bits);

module mkBug166();
  Reg#(Bool) tick();
  mkReg#(False) tick_inst(tick);
  Reg#(Quux#(bit[31:0])) r();
  mkReg#(?) r_inst(r);
  
  rule update_foo (tick);
    Quux#(bit[31:0]) tmp = r;
    tmp.foo = tmp.foo + 1;
    r <= tmp;
    tick <= !tick;
  endrule
  rule update_bar (!tick);
    Quux#(bit[31:0]) tmp = r;
    tmp.bar = tmp.bar + 1;
    r <= tmp;
    tick <= !tick;
  endrule
endmodule
