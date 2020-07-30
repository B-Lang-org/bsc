(* synthesize *)
module sysx () ;
  InterfaceTest i <- usesGo();
  Reg#(int) jni <- mkRegU();
  rule foobar;
        i.go();
        let foo <- i.av();
        $display(foo);


  endrule
endmodule

interface InterfaceTest ;
        method Action go();
        method int justInt();
        method ActionValue#(int) av();
endinterface

module usesGo(InterfaceTest);
        Reg#(Bool) x <- mkRegU();
        Reg#(int) ii <- mkRegU();
        Reg#(int) jj <- mkRegU();
   method go ;
              (* split *)
        action      
        if (x)
                ii <= 10;
        else
                ii <= 20;
        endaction
        endmethod

        method justInt = 17;

        method av ;
        actionvalue
        if (x)
                jj <= 100;
        else
                jj <= 200;
        return 22;
        endactionvalue

        endmethod

endmodule
