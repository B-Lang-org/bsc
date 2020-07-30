
function Bit#(8) selectFn(Bit#(32) vec, Bit#(2) idx);
   case (idx)
      0: return vec[7:0];
      1: return vec[15:8];
      2: return vec[23:16];
      default: return vec[31:24];
   endcase
endfunction

(* synthesize *)
module sysIfElseCase_Func ();

   Reg#(Bit#(2)) r_idx <- mkReg(0);
   Reg#(Bit#(32)) r_vec <- mkReg(32'hAABBCCDD);

   rule r;
      Bit#(8) tmp;
      if (r_idx == 0)
         tmp = 0;
      else begin
         tmp = selectFn(r_vec, r_idx);
      end
      $displayh(tmp);

      r_idx <= r_idx + 1;
      if (r_idx == 3)
         $finish(0);
   endrule

endmodule

