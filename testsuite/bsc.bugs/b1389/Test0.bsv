import GetPut :: * ;
import FIFOF :: * ;


typedef struct {
                int a;
                int b;
   } Foo
deriving (Bits) ;

(* synthesize *)
module mkTest ( GetPut#(Foo) );
   
   FIFOF#(Foo) f <- mkFIFOF ;
   Reg#(Bool)  p <- mkReg(False);
   
   rule c (!p) ;
      f.deq ;
   endrule
   
   interface Get fst ;
      method ActionValue#(Foo) get ();
            (*split*)
         if (p) 
            begin
               Foo r = f.first ;
               f.deq ;
               return r;
            end
         else return unpack(0);
      endmethod


   endinterface
   
   interface Put snd ;
      method Action put (Foo d );
         f.enq (d);
      endmethod
   endinterface
endmodule
