(* synthesize *)
module sysCaseCase();
   Reg#(Bit#(3)) rg <- mkReg(0);
   Reg#(Bit#(8)) rg2 <- mkRegU;
   rule r;
      Bit#(8) n;
      case (rg)
         0 : n = 17;
         1 : n = 42;
         2 : n = 2;
         default :
            case (rg)
               3: n = 22;
               4: n = 23;
               default : n = 5;
            endcase
      endcase
      rg2 <= n;
   endrule
endmodule
