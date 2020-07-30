interface ArithIO_IFC #(parameter type aTyp);
    method Action start(aTyp num1, aTyp num2);
    method aTyp result();
endinterface: ArithIO_IFC

(* synthesize *)
module mkGCD(ArithIO_IFC#(UInt#(16)));

    Reg#(UInt#(16)) x <- mkRegU;
    Reg#(UInt#(16)) y <- mkReg(0);

    rule swap (x > y && y != 0);
        x <= y;
        y <= x;
    endrule

    rule subtract (x <= y && y != 0);
        y <= y - x;
    endrule

    method Action start(UInt#(16) num1, UInt#(16) num2) if (y == 0);
        x <= num1;
        y <= num2;
    endmethod: start

    method UInt#(16) result() if (y == 0);
        return x;
    endmethod: result

endmodule: mkGCD
