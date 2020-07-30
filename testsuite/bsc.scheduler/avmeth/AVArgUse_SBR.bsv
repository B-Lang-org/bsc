// Should deduce (m SBR m) for this AV method, which does not use
// an argument in the return value

interface Ifc;
   method ActionValue#(Bool) m(int a, int b);
endinterface

(* synthesize *)
module mkAVArgUse_SBR(Ifc);
    Reg#(Bool) rg <- mkRegU;
    Reg#(Bool) rg2 <- mkRegU;

    method ActionValue#(Bool) m(int a, int b);
        rg <= (a == b);
	// returning rg would cause a conflict,
	// so return another value
        return rg2;
    endmethod
endmodule

(* synthesize *)
module sysAVArgUse_SBR();
    let dut <- mkAVArgUse_SBR();
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

