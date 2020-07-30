interface Converter#(type i);
   method Tuple2#(i, i) convert(i arg);
endinterface

interface VConverter#(numeric type ni);
   method Bit#(mi) convert(Bit#(ni) arg);
endinterface


import "BVI" Mod = 
  module vMkConverter(VConverter#(ni));
     method OUT m(IN);
  endmodule


module mkConverter(Converter#(i)) provisos(Bits#(i, si));

  VConverter#(si) _a <- vMkConverter;
   
  method convert(i);
     return(unpack(_a.convert(pack(i))));
  endmethod

endmodule
