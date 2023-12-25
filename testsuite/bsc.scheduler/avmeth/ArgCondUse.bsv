typedef Int#(32) T;

interface Ifc;
    method Action m(T value);
endinterface

(* synthesize *)
module mkArgCondUse (Ifc);
    Reg#(T) r <- mkReg(0);

    method Action m(T value);
        if (value > 0) begin
            r <= value;
        end
    endmethod
endmodule
