import StmtFSM::*;

(*synthesize*)
module sysSaturateArith();

   //////////////////////////////////////////////
   //   Test of add and sub sat
   function Stmt addTestI (Reg#(Int#(n)) x, Reg#(Int#(n)) y);
      return
      (seq
       for (x <= minBound ; True;  x <= x + 1)
          seq
             for (y <= minBound ; True;  y <= y + 1)
                seq
                   action
                      Int#(n) x1 = satPlus(Sat_Wrap, x,y);
                      Int#(n) x2 = satPlus(Sat_Bound, x,y);
                      Int#(n) x3 = satPlus(Sat_Zero, x,y);
                      Int#(n) x4 = satPlus(Sat_Symmetric, x,y);
                      Int#(n) s1 = satMinus(Sat_Wrap, x,y);
                      Int#(n) s2 = satMinus(Sat_Bound, x,y);
                      Int#(n) s3 = satMinus(Sat_Zero, x,y);
                      Int#(n) s4 = satMinus(Sat_Symmetric, x,y);
                      $display ("%d %d:   %d %d %d %d    %d %d %d %d", x,  y,
                         x1,x2,x3,x4
                         ,s1,s2,s3,s4
                         );
                   endaction
                   if (y == maxBound) break;
                endseq
             $display ("-------");
             if (x == maxBound) break;
          endseq
       endseq);
   endfunction

   function Stmt addTestG (Reg#(t) x, Reg#(t) y)
   provisos( Arith#(t), Bounded#(t), SaturatingArith#(t), Eq#(t), Bits#(t,st) );
      return
      (seq
       for (x <= minBound ; True;  x <= x + 1)
          seq
             for (y <= minBound ; True;  y <= y + 1)
                seq
                   action
                      t x1 = satPlus(Sat_Wrap, x,y);
                      t x2 = satPlus(Sat_Bound, x,y);
                      t x3 = satPlus(Sat_Zero, x,y);
                      t x4 = satPlus(Sat_Symmetric, x,y);
                      t s1 = satMinus(Sat_Wrap, x,y);
                      t s2 = satMinus(Sat_Bound, x,y);
                      t s3 = satMinus(Sat_Zero, x,y);
                      t s4 = satMinus(Sat_Symmetric, x,y);
                      $display ("%d %d:   %d %d %d %d    %d %d %d %d", x,  y,
                         x1,x2,x3,x4
                         ,s1,s2,s3,s4
                         );
                   endaction
                   if (y == maxBound) break;
                endseq
             $display ("-------");
             if (x == maxBound) break;
          endseq
       endseq);
   endfunction

   Reg#(Int#(3))  xi <- mkReg(0);
   Reg#(Int#(3))  yi <- mkReg(0);
   Reg#(UInt#(3))  xu <- mkReg(0);
   Reg#(UInt#(3))  yu <- mkReg(0);

   let tester =
   (seq
    $display ("Int  Sat addtions");
       addTestI(xi, yi);

    $display ("UInt  Sat addtions");
       addTestG(xu, yu);

    endseq);

   mkAutoFSM(tester);

endmodule
