(* synthesize *)
module sysCompareSameExpr ();

    Reg#(Bit#(2)) rg <- mkRegU;

    rule rUEQ;
      if (rg == rg) begin
        $display("rUEQ");
      end
    endrule

    rule rUNE;
      if (rg != rg) begin
        $display("rUNE");
      end
    endrule

    rule rULT;
      if (rg < rg) begin
        $display("rULT");
      end
    endrule

    rule rULE;
      if (rg <= rg) begin
        $display("rULE");
      end
    endrule

    rule rUGT;
      if (rg > rg) begin
        $display("rUGT");
      end
    endrule

    rule rUGE;
      if (rg >= rg) begin
        $display("rUGE");
      end
    endrule

    // Test signed versions
    Reg#(Int#(2)) rg_s <- mkRegU;

    rule rSEQ;
      if (rg_s == rg_s) begin
        $display("rSEQ");
      end
    endrule

    rule rSNE;
      if (rg_s != rg_s) begin
        $display("rSNE");
      end
    endrule

    rule rSLT;
      if (rg_s < rg_s) begin
        $display("rSLT");
      end
    endrule

    rule rSLE;
      if (rg_s <= rg_s) begin
        $display("rSLE");
      end
    endrule

    rule rSGT;
      if (rg_s > rg_s) begin
        $display("rSGT");
      end
    endrule

    rule rSGE;
      if (rg_s >= rg_s) begin
        $display("rSGE");
      end
    endrule

endmodule