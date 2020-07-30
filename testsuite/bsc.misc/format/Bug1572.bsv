import FShow::*;

typedef enum {Exists,Initialized,Operating}  WCI_STATE deriving (Bits, Eq);

instance FShow#(WCI_STATE);
  function Fmt fshow (WCI_STATE state);
    case (state)
      Exists:      return fshow("Exists ");
      Initialized: return fshow("Initialized ");
      Operating:   return fshow("Operating ");
    endcase
  endfunction
endinstance

function WCI_STATE incr(WCI_STATE x);
   case (x)
      Exists: return Initialized;
      Initialized: return Operating;
      Operating: return Exists;
   endcase
endfunction

(* synthesize *)
module sysBug1572 ();
  Reg#(WCI_STATE)               cState           <- mkReg(Exists);
  Reg#(WCI_STATE)               nState           <- mkReg(Exists);

  rule r;
    $display("Completed ", fshow(cState), " transition from ", fshow(nState));
    if (cState == Operating) begin
      if (nState == Operating)
        $finish(0);
      nState <= incr(nState);
    end
    cState <= incr(cState);
  endrule

endmodule
