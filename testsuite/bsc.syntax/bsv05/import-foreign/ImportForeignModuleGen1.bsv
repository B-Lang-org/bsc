interface VReg #(type n);
    method Action set(Bit#(n) x1);
    method Bit#(n) get();
endinterface: VReg

(* synthesize *)
import "BVI" MyRegN = module vMkReg#(Integer nn, Bit#(n) v)(VReg#(n));
  default_clock clk(CLK);
  parameter width = nn;
  parameter init = v;
  method (* reg *)Q_OUT get();
  method set(D_IN) enable(EN);
  schedule get CF get;
  schedule get SB set;
  schedule set SBR set;
endmodule: vMkReg

