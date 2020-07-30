
import Sub::* ;


(* synthesize *)
module tbSub( Empty ) ;
// create an interface
        ArithIO #( Sub_t ) ifc() ;
// instantiate the module
        msub xI1 ( ifc ) ;


// instantiate some test registers
        Reg #(Sub_t ) data1();
        mkReg#(0) iI1xxx(data1) ;
        Reg #(Sub_t)  data2() ;
        mkReg#(0) iI2yyy(data2) ;

        rule top (True) ;
          ifc.start( data1, data2 ) ;
          data1 <= data1 - 1;
          data2 <= data2 - 2;
        endrule: top 

endmodule : tbSub
