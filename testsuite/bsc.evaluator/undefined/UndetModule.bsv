Module#(Reg#(Bool)) mkM = ?;

(* synthesize *)
module sysUndetModule(Reg#(Bool));
    Reg#(Bool) rg <- mkM;
    return rg;
endmodule
