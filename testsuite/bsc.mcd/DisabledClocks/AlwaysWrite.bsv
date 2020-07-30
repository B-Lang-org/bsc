interface WriteOnly#(type a);
   method Action _write(a v);
endinterface

// module with an always-enabled port to tie to a default value
import "BVI" AlwaysWrite = 
   module mkAlwaysWrite(WriteOnly#(a)) provisos(Bits#(a,sa));
     no_reset;
     parameter width = valueof(sa);
     method _write(D_IN) enable((*inhigh*)EN);
     schedule _write C _write;
endmodule
