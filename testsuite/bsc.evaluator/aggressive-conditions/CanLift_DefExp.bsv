import FIFOF::*;

typedef 32 SZ;

(* synthesize *)
module sysCanLift_DefExp ();

    FIFOF#(Bool) link_resp_fifo <- mkFIFOF();

    Reg#(Bit#(SZ)) chunk <- mkReg(0);

    function ActionValue#(Bit#(SZ)) readAndDelete();
     actionvalue
        Bit#(SZ) final_val = 0;
        for (Integer x = 0; x < valueOf(SZ); x = x + 1)
        begin
            Integer k = x % valueOf(SZ);
            final_val[x] = chunk[k];
        end
        return unpack(final_val);
     endactionvalue
    endfunction

  // (* conservative_implicit_conditions *)
  rule r;
    let req <- readAndDelete();
    case (req)
     0: link_resp_fifo.enq(True);
     1: link_resp_fifo.enq(False);
    endcase
  endrule

endmodule

