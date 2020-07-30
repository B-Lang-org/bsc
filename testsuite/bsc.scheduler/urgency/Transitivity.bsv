// Test for bug 649

// This results in a warning about an arbitrary order between 1 and 3
(*descending_urgency = "r1, r2",
  descending_urgency = "r2, r3" *)

// While this does not:
//(* descending_urgency = "r1, r2, r3" *)

(* synthesize *)
module sysTransitivity();

    Reg#(Bool) p1 <- mkRegU;
    Reg#(Bool) p2 <- mkRegU;
    Reg#(Bool) p3 <- mkRegU;

    Reg#(int) rg1 <- mkRegU;
    Reg#(int) rg2 <- mkRegU;

    rule r1 (p1);
	rg1 <= rg1 + 1;
	rg2 <= rg2 + 1;
    endrule
    
    rule r2 (p2);
	rg1 <= rg1 + 2;
    endrule

    rule r3 (p3);
	rg2 <= rg2 + 3;
    endrule

endmodule

