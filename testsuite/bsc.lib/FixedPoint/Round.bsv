
import FixedPoint::*;
import FShow::*;
import StmtFSM::*;

(*synthesize*)
module sysRound();

   Reg#(FixedPoint#(2,3))  cnt <- mkReg(minBound);
   Reg#(FixedPoint#(4,1))  cnt41 <- mkReg(minBound);
   Reg#(SaturationMode) smode <- mkReg(Sat_Wrap);

   let printer =
   (action
      $write(fshow(cnt), " ");
      fxptWrite(3,cnt);  $write(":   ");
      for (Integer i =0 ; i < 7; i = i + 1) begin
         $write("\t");
         RoundMode mode = unpack(fromInteger(i));
         FixedPoint#(2,1) r = fxptTruncateRoundSat(mode, smode, cnt);
         fxptWrite(3,r);
      end
      $display(";");
    endaction);
   
   let dropMSB =
   (action
       $write(fshow(cnt41), " ");
       fxptWrite(2,cnt41);  $write(":   ");
       for (Integer i =0 ; i < 4; i = i + 1) begin
          $write("\t");
          SaturationMode smode = unpack(fromInteger(i));
          $write("\t");
          FixedPoint#(2,1) r = fxptTruncateSat(smode, cnt41);
          fxptWrite(2,r);
       end
       $display(";");
    endaction);
   
   let tester =
   (seq
       smode <= Sat_Wrap;
       $display( "Sat_Wrap mode");
       for(cnt <= minBound; cnt != maxBound; cnt <= cnt + epsilon)
          printer;
       printer;

       smode <= Sat_Bound;
       $display( "Sat_Bound mode");
       for(cnt <= minBound; cnt != maxBound; cnt <= cnt + epsilon)
          printer;
       printer;

       smode <= Sat_Zero;
       $display( "Sat_Zero mode");
       for(cnt <= minBound; cnt != maxBound; cnt <= cnt + epsilon)
          printer;
       printer;

       smode <= Sat_Symmetric;
       $display( "Sat_Symmetric mode");
       for(cnt <= minBound; cnt != maxBound; cnt <= cnt + epsilon)
          printer;
       printer;
    
       $display ("Droping MSB bit with fxptTruncateSat");
       for(cnt41 <= minBound; cnt41 != maxBound; cnt41 <= cnt41 + epsilon)
          dropMSB;
       dropMSB;
    
       $display ("Zero bit drops");
       action 
          FixedPoint#(2,3) foo = fxptTruncateRoundSat(Rnd_Inf, Sat_Bound, cnt);
          $display (fshow(cnt41), fshow(foo));
          FixedPoint#(4,1) bar = fxptTruncateSat(Sat_Bound,cnt41);
          $display (fshow(cnt41), fshow(bar));
       endaction
    endseq);

   mkAutoFSM(tester);

endmodule
