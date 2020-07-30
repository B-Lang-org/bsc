export Divisible_IFC(..);
export mkDIV3;

interface Divisible_IFC;
    method Action nextDigit(Int#(32) x1);
    method Bool isDivisible();
endinterface: Divisible_IFC

(* synthesize *)
module mkDIV3(Divisible_IFC);
  Reg#(Int#(32)) y();
  mkReg#(0) the_y(y);
  Reg#(Bool) z();
  mkReg#(False) the_z(z);
  Reg#(Bool) resIsReady();
  mkReg#(False) the_resIsReady(resIsReady);

  rule rule1_subractaway (y != 0 && y != 1 && y != 2);
      y <= y - 3;
      resIsReady <= False;
  endrule: rule1_subractaway

  rule rule2_notDivByThree (y == 1 || y == 2);
      z <= False;
      resIsReady <= True;
  endrule: rule2_notDivByThree

  rule rule3_isDivByThree (y == 0);
      z <= True;
      resIsReady <= True;
  endrule: rule3_isDivByThree

  method nextDigit(inum) if (resIsReady == True);
    action
      y <= inum;
      resIsReady <= False;
    endaction
  endmethod: nextDigit

  method isDivisible() if (resIsReady == True); 
    return (z);
  endmethod: isDivisible
endmodule: mkDIV3


