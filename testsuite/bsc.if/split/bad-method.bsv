module sysx () ;
  InterfaceTest i <- usesGo();
  rule foobar;
        i.go();
  endrule
endmodule

interface InterfaceTest ;
        method Action go();
endinterface

(* synthesize *)
module usesGo(InterfaceTest);
        Reg#(Bool) x <- mkRegU();
        Reg#(int) ii <- mkRegU();
        (*split*)
        method go ;
        action
        if (x)
                ii <= 10;
        else
                ii <= 20;
        endaction
        endmethod
endmodule

