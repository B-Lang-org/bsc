package Design;

import Interface::*;

interface Design_in_IFC;
    method Action calc(
                       Bit#(1) x,
                       Bit#(1) y
                      );
    method Bit#(1) result ();
endinterface: Design_in_IFC


interface   Design_IFC;
    method Action calc(
                       Bit#(1) aa,
                       Bit#(1) ab,
                       Bit#(1) ba,
                       Bit#(1) bb
                      );
    method Bit#(1) result_adder1();
    method Bit#(1) result_adder2();
endinterface: Design_IFC



interface Joint_IFC;
   interface Design_in_IFC one ;
   interface Design_IFC two;
endinterface


(* synthesize *)
module mkDesign2( Design_IFC2#(Bit#(2)) );
endmodule       

      
(* synthesize *)
module foo( Joint_IFC );
endmodule       
      
(* synthesize *)
module mkDesign_in (Design_in_IFC);

    Reg#(Bit#(1))   sum();
    mkReg#(0)   i_sum(sum);

    method Action calc(
                       Bit#(1) x1,
                       Bit#(1) y1
                      );
        action
            sum <=  x1 + y1;
        endaction
    endmethod

    method Bit#(1) result ();
        result = sum;
    endmethod: result

endmodule: mkDesign_in


(*  synthesize,
    always_ready,
    always_enabled,
    CLK = "clk",
    RST_N = "reset"
*)
module mkDesign (Design_IFC);

    Reg#(Bit#(1)) a0();
    mkReg#(0) i_a0(a0);

    Reg#(Bit#(1)) a1();
    mkReg#(0) i_a1(a1);

    Reg#(Bit#(1)) b0();
    mkReg#(0) i_b0(b0);

    Reg#(Bit#(1)) b1();
    mkReg#(0) i_b1(b1);

    Reg#(Bit#(1)) res1();
    mkReg#(0) i_res1(res1);

    Reg#(Bit#(1)) res2();
    mkReg#(0) i_res2(res2);

    method Action calc(
                       Bit#(1) aa,
                       Bit#(1) ab,
                       Bit#(1) ba,
                       Bit#(1) bb
                      );
        action
            a0      <=  aa;
            a1      <=  ab;
            b0      <=  ba;
            b1      <=  bb;
            res1    <= a0 ^ a1;
            res2    <= b0 ^ b1;
        endaction
    endmethod

    method Bit#(1) result_adder1();
        result_adder1 = res1;
    endmethod

    method Bit#(1) result_adder2();
        result_adder2 = res2;
    endmethod
    
endmodule

endpackage

