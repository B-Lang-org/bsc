import Complex :: *;
import StmtFSM :: *;

typedef Int#(16) MYT ;
typedef Complex#(MYT) MYC;

(* synthesize *)
module sysSRAConst ();

   Reg#(Bool) go <- mkReg(False);
   Reg#(MYC) r1 <- mkReg( Complex { rel: minBound, img : minBound });

   rule s1 (go);
      MYT i = r1.img;
      MYT r = r1.rel;
      $display ( "Base:  %h %h", i, r );
      for ( Integer j = 0; j < 40; j = j + 4 )
         begin
            MYT i10 = r1.img >> j ;
            MYT r10 = r1.rel >> j ;
            $display (  "Shift by %d   ->  %h  %h", j, i10, r10 );
         end
   endrule

   Stmt testseq =
   (seq
       action
          go <= True ;
          r1<= Complex { rel: minBound, img : minBound };
       endaction
       r1<= Complex { rel: 0, img : 0 };
       r1<= Complex { rel: maxBound, img : maxBound };
    endseq);

   mkAutoFSM( testseq) ;

endmodule
