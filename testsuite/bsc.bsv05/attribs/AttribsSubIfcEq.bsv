interface Ifc;
   interface Reg#(Bool) r;
endinterface

module mkMod(Ifc);
   (* foo *)
   interface r = ?;
endmodule


