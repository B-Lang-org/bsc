// Should deduce (m C m) for an AV method which uses an argument
// in the return value

interface Ifc;
   method ActionValue#(Bool) m(int a, int b);
endinterface

(* synthesize *)
module mkAVArgUse_C(Ifc);
    Reg#(int) rg <- mkRegU;

    method ActionValue#(Bool) m(int a, int b);
        rg <= a;
        return (a == b);
    endmethod
endmodule

(* synthesize *)
module sysAVArgUse_C();
    let dut <- mkAVArgUse_C();
    Reg#(int) r1 <- mkReg(0); 

    rule rA;
        let v1 <- dut.m(r1, 1);
        $display($stime, " rA ", v1);
        r1 <= r1 + 1;
        if (r1 == 10) $finish;
    endrule 

    rule rB;
        let v2 <- dut.m(5, r1);
        $display($stime, " rB ", v2);
    endrule
endmodule

