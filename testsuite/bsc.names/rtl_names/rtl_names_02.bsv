interface RTL_Names_02;
    method Action m1();
endinterface: RTL_Names_02

(* doc="if x_y is preserved in RTL, it should be called x_y, not _d3" *)
(* synthesize *)
module rtl_names_02(RTL_Names_02);
    Reg#(bit) r_x <- mkRegU;
    Reg#(bit) r_y <- mkRegU;
    
    method Action m1;
        let x_y = r_x & r_y;
        r_x <= x_y;
        r_y <= x_y;
    endmethod: m1
endmodule: rtl_names_02
