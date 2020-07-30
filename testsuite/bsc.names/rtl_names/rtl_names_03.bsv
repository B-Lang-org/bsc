(* doc="if x_y is preserved in RTL, it should be called x_y, not _d3" *)
(* synthesize *)
module rtl_names_03();
    Reg#(bit) r_x <- mkRegU;
    Reg#(bit) r_y <- mkRegU;

    function f1();
        action
            let x_y = r_x & r_y;
            r_x <= x_y;
            r_y <= x_y;
        endaction
    endfunction: f1

    rule r1;
        f1();
    endrule

    rule r2;
        f1();
    endrule
endmodule: rtl_names_03
