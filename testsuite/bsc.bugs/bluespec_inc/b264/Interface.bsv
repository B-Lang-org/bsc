package Interface ;

interface   Design_IFC2 #(parameter type aType);
    method Action calc2(
                       aType   aa,
                       Bit#(1) ab,
                       Bit#(1) ba,
                       Bit#(1) bb
                      );
    method Bit#(1) result2_adder1();
    method Bit#(1) result2_adder2();
endinterface: Design_IFC2

endpackage
