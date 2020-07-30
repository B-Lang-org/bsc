(* doc="if x_y is preserved in RTL, it should be called x_y, not _d3" *)
(* synthesize *)
module rtl_names_04();
    Reg#(bit) r_x <- mkRegU;
    Reg#(bit) r_y <- mkRegU;

    int i;
    for (i=0; i < 2; i = i + 1) begin
        rule r;
            let x_y = r_x & r_y;
            r_x <= x_y;
            r_y <= x_y;
        endrule
    end
endmodule: rtl_names_04
