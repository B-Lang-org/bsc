(* doc="if x_y is preserved in RTL, it should be called x_y, not _d3" *)
(* synthesize *)
module rtl_names_01();
    Reg#(int) r_x <- mkRegU;
    Reg#(int) r_y <- mkRegU;
    
    rule r1;
        let x_y = r_x & r_y;
        r_x <= x_y;
        r_y <= x_y;
    endrule
endmodule: rtl_names_01
