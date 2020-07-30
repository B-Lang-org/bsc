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
  mkId the_id(idIfc);
  rule bogus;
    idIfc.id(noAction);
  endrule
endmodule
