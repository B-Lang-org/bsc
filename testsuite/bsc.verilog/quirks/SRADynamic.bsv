import Complex :: *;
import StmtFSM :: *;

typedef Int#(16) MYT ;
typedef Complex#(MYT) MYC;

(* synthesize *)
module sysSRADynamic ();


   Reg#(MYC) r1 <- mkReg( Complex { rel: minBound, img : minBound });
   Reg#(UInt#(10))  sa <- mkReg(maxBound);

   Stmt loopseq =
   (seq
       $display ( "Base:  %h %h", r1.img, r1.rel );
       sa <= 0;
       while ( sa < 40 )
          seq
             action
                sa <= sa + 4 ;

                MYT i = r1.img;
                MYT r = r1.rel;

                MYT i10 = r1.img >> sa ;
                MYT r10 = r1.rel >> sa ;

                $display (  "Shift by %d   ->  %h  %h", sa, i10, r10 );
             endaction
          endseq
    endseq);

   Stmt testseq =
   (seq
       r1<= Complex { rel: minBound, img : minBound };
       loopseq;
       r1<= Complex { rel: 0, img : 0 };
       loopseq;
       r1<= Complex { rel: maxBound, img : maxBound };
       loopseq;

    endseq);

   mkAutoFSM( testseq) ;


endmodule
