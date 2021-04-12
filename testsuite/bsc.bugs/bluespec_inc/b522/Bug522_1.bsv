interface Pat_IFC;

method Bit#(1) out (Bit#(2) in1, Bit#(2) in2);

endinterface: Pat_IFC

(*
    always_enabled,
    always_ready,
    CLK = "clk",
    RST_N = "reset"
*)

module mkPat(Pat_IFC);

method Bit#(1) out (Bit#(2) in1, Bit#(2) in2);
  Bit#(2) a = 2;
     if (in1[0] == 1)
        a = 2;
     else if (in1[1] == 1)
        a = 2;

     if (in2[0] == 1)
        a = 3;
     else if (in2[1] == 1)
        a = 3;

  out = a[0];
endmethod

endmodule: mkPat
