

import StmtFSM ::*;


typedef struct {
                Bool btag;
                UInt#(5) ok;
                } Foo
deriving (Bits);

// Declare !=
instance Eq #(Foo);
   function \/= (Foo x, Foo y);
      return (x.ok != y.ok);
   endfunction
endinstance

(*synthesize*)
module sysEq2 ();
   Reg#(Foo) x <- mkReg(unpack(0));
   Reg#(Foo) y <- mkReg(unpack(0));
   
   function Foo mkfoo (Bool xx, UInt#(5) yy);
      return Foo { btag:xx, ok:yy };
   endfunction
   function Action test() ;
      $display ( "%x %d <?> %x %d --> %d", 
                x.btag, x.ok,
                y.btag, y.ok,
                x == y);
   endfunction
   
   Stmt testseq =
   (seq
       x <= mkfoo(True,0);
       test;
       x <= mkfoo(True,1);
       test;
       x <= mkfoo(True,4);
       test;
       y <= mkfoo(True,4);
       test;
       x <= mkfoo(False,4);
       test;
       x <= mkfoo(False,1);
       test;
       x <= mkfoo(False,4);
       test;
    endseq);
   
   mkAutoFSM(testseq);
endmodule
