(* synthesize *)
module sysParamSizeDefault #(parameter Bit#(2) b) ();
    Reg#(Bit#(3)) c <- mkReg(0);

    Bit#(5) a = {c, b};

    rule r;
        c <= c + 1;
        $display("a = %b", a);
        if (c > 5) $finish(0);
    endrule
endmodule

