(* doc="if x_0 is preserved in RTL, it should be called x_y, not _d3" *)
(* synthesize *)
module rtl_names_11();
    Reg#(bit[3:0]) r_x <- mkRegU;
    
    rule r1;
        let x_zero = r_x[0];
        r_x[1] <= x_zero; // & r_y;
    endrule
endmodule: rtl_names_11
