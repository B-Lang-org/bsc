typedef Bit#(32) Addr;

(* synthesize *)
module mkFOO(Empty);

Reg#(Addr) addr<- mkReg(?);

rule go(True);
 case (addr) matches
  32'h_0000_000?: $display("a");
  32'h_0000_001?: $display("b");
  32'h_0000_002?: $display("c");
  32'h_0000_048?: $display("d");
  32'h_0000_480?: $display("e");
  default:        $display("f");
 endcase
endrule


endmodule
