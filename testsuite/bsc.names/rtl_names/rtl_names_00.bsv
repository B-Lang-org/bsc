(* doc="if x_y is preserved in RTL, it should be called x_y, not _d3" *)
(* synthesize *)
module rtl_names_00();
    Reg#(bit) r_x <- mkRegU;
    Reg#(bit) r_y <- mkRegU;
    
    let x_y = r_x & r_y;
    
    rule r1;
        r_x <= x_y;
        r_y <= x_y;
    endrule
endmodule: rtl_names_00
