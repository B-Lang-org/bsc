interface Ifc;
   interface Reg#(Bool) r;
endinterface

module mkMod(Ifc);
   (* foo *)
   interface Reg r;
      method _read = ?;
      method _write = ?;
   endinterface
endmodule


