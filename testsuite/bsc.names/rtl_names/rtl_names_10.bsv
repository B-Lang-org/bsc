(* doc="if r[0] is preserved in RTL, it should be called r_0, not _d3" *)
(* synthesize *)
module rtl_names_10();
    Reg#(bit[3:0]) r <- mkRegU;
    
    rule r1;
        r[1] <= r[0];
    endrule
endmodule: rtl_names_10
