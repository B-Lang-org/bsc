import Vector::*;

typedef 200 Size;

Integer size = valueof(Size);

interface Val;
  method Bit#(32) val;
endinterface

interface ManyMeths;
  interface Vector#(Size, Val) vals;
endinterface

(* options="-no-show-method-conf" *)
(* synthesize *)
module sysManyMeths(ManyMeths);

  Vector#(Size, Val) vals_ifcs = ?;

  for(Integer i = 0; i < size; i = i + 1)
  begin
    vals_ifcs[i] = interface Val;
                     method val = fromInteger(i);
                   endinterface;
  end

  interface vals = vals_ifcs;

endmodule

