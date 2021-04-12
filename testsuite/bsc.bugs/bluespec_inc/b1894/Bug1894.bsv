typedef struct {
  Bit#(8) imm;
  Maybe#(Bit#(2)) checkPoint;
} RenamedInst deriving (Eq, Bits);

interface Ifc;
  method ActionValue#(Bit#(2)) m();
endinterface

(* synthesize *)
module mkSub(Ifc);
  method ActionValue#(Bit#(2)) m();
    return 2'b11;
  endmethod
endmodule

(* synthesize *)
module mkTop();
  Ifc s <- mkSub;

  Reg#(Bool) cond <- mkReg(False);

  Reg#(RenamedInst) rg <- mkRegU;

  Reg#(Bool) done <- mkReg(False);

  rule do_disp (!done);
    RenamedInst x;
    x.imm = 0;
    x.checkPoint = tagged Invalid;

    if (cond) begin
      let v <- s.m;
      x.checkPoint = tagged Valid v;
    end

    $display("%h", x);
    done <= True;
  endrule

  rule do_finish (done);
    $finish(0);
  endrule
endmodule
