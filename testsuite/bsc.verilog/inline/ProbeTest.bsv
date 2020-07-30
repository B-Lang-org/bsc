import Probe::* ;

(* synthesize *)
module sysProbeTest ();

 Reg#(Bit#(12)) regA <- mkReg(0);
 Reg#(Bit#(4))  regB <- mkReg(0);
 
 Probe#(Bit#(5)) x <- mkProbe;

 rule test_rule;
    Bit#(5) y = 0 ;
    Bit#(5) z = 0 ;
    if (regA == 1)
       begin
	  regB <= 0;
       end
    else if (regA == 2)
       begin
	  regB <= 1;
	  x <= truncate(regA);
       end
    else
       begin
	  regA <= regA + 1;
       end
 endrule

endmodule

