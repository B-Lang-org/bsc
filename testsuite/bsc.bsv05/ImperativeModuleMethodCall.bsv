interface Id;
  method a id(a x);
endinterface

module mkId(Id);
  method a id(a x);
    id = x;
  endmethod
endmodule

module mkFoo();
  Id idIfc();
  mkId theId(idIfc);
  idIfc.id(mkFoo());
endmodule

