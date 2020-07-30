(* synthesize *)
module sysx () ;
  InterfaceTest i <- usesGo();

  InterfaceTest i2 <- usesGo();

  Reg#(int) jni <- mkRegU();
  rule ruleOne;
        (*split*)
        i.go();
  endrule

  rule ruleTwo;
        i2.go();
  endrule

endmodule

interface InterfaceTest ;
        method Action go();
endinterface

module usesGo(InterfaceTest);
        Reg#(Bool) x <- mkRegU();
        Reg#(int) ii <- mkRegU();
        method go ;
        action
        if (x)
                ii <= 10;
        else
                ii <= 20;
        endaction
        endmethod
endmodule

