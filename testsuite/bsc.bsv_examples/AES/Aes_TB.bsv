import Defines::*;
import Aes::*;
import StmtFSM::*;
import FIFOF::*;
import LFSR :: * ;
import RegFile::*;

// (setq   bsc-compile-command "bsc  -steps 500000 -u -verilog -cross-info -aggressive-conditions -i +:../common -p +:../common -I +:../common")

(* synthesize *)
module sysAes_TB ();
   
   RegFile#(Bit#(8),Bit#(128)) datFile      <- mkRegFileLoad("dat.vectors", 0, 255);

   RegFile#(Bit#(8),Bit#(128)) keyFile128   <- mkRegFileLoad("key128.vectors", 0, 255);
   RegFile#(Bit#(8),Bit#(192)) keyFile192   <- mkRegFileLoad("key192.vectors", 0, 255);
   RegFile#(Bit#(8),Bit#(256)) keyFile256   <- mkRegFileLoad("key256.vectors", 0, 255);

   Aes aes <- mkAes;

   FIFOF#(UWORD) retData <- mkSizedFIFOF(8);

   Reg#(Bit#(8)) ii <- mkReg(0);
   Reg#(UWORD) r0 <- mkReg(0);
   Reg#(UWORD) r1 <- mkReg(0);
   Reg#(UWORD) r2 <- mkReg(0);
   Reg#(UWORD) r3 <- mkReg(0);

   Reg#(UWORD) new0 <- mkReg(0);
   Reg#(UWORD) new1 <- mkReg(0);
   Reg#(UWORD) new2 <- mkReg(0);
   Reg#(UWORD) new3 <- mkReg(0);
   Reg#(UWORD) new4 <- mkReg(0);
   Reg#(UWORD) new5 <- mkReg(0);
   Reg#(UWORD) new6 <- mkReg(0);
   Reg#(UWORD) new7 <- mkReg(0);

   Reg#(UWORD) matchCnt <- mkReg(0);
   Reg#(UWORD) errorCnt <- mkReg(0);

   /*
   function Stmt driveKey256( Bit#(256) key );
   return seq
             aes.dbus.push( Encrypt256( key[255:224] ) );
             aes.dbus.push( Encrypt256( key[223:192] ) );
             aes.dbus.push( Encrypt256( key[191:160] ) );
             aes.dbus.push( Encrypt256( key[159:128] ) );
             aes.dbus.push( Encrypt256( key[127:96] ) );
             aes.dbus.push( Encrypt256( key[95:64] ) );
             aes.dbus.push( Encrypt256( key[63:32] ) );
             aes.dbus.push( Encrypt256( key[31:0] ) );
          endseq;
   endfunction
   
   
   function Stmt driveKey192( Bit#(192) key );
   return seq
             aes.dbus.push( Encrypt192( key[191:160] ) );
             aes.dbus.push( Encrypt192( key[159:128] ) );
             aes.dbus.push( Encrypt192( key[127:96] ) );
             aes.dbus.push( Encrypt192( key[95:64] ) );
             aes.dbus.push( Encrypt192( key[63:32] ) );
             aes.dbus.push( Encrypt192( key[31:0] ) );
          endseq;
   endfunction
   */
   
   function Stmt test( Bit#(n) key, Bit#(128) data ) ;
      return seq
                aes.dbus.push( Encrypt128( key[127:96] ) );
                aes.dbus.push( Encrypt128( key[95:64] ) );
                aes.dbus.push( Encrypt128( key[63:32] ) );
                aes.dbus.push( Encrypt128( key[31:0] ) );

                /////////////////////////////////////////////
                aes.dbus.push( Encrypt128( data[127:96] ) );
                aes.dbus.push( Encrypt128( data[95:64] ) );
                aes.dbus.push( Encrypt128( data[63:32] ) );
                aes.dbus.push( Encrypt128( data[31:0] ) );

                // r0 = word of encrypted data returned by Encrypt128
                action r0 <= retData.first(); retData.deq(); endaction
                action r1 <= retData.first(); retData.deq(); endaction
                action r2 <= retData.first(); retData.deq(); endaction
                action r3 <= retData.first(); retData.deq(); endaction
                
                // decrypter with same key

                aes.dbus.push( Decrypt128( key[127:96] ) );
                aes.dbus.push( Decrypt128( key[95:64] ) );
                aes.dbus.push( Decrypt128( key[63:32] ) );
                aes.dbus.push( Decrypt128( key[31:0] ) );

                // pass back the encrypted data we got from Encrypt128
                aes.dbus.push( Decrypt128( r0 ) );
                aes.dbus.push( Decrypt128( r1 ) );
                aes.dbus.push( Decrypt128( r2 ) );
                aes.dbus.push( Decrypt128( r3 ) );

                // AES runs for ??? cycles

                // new = word of deccrypted data returned by Decrypt128
                // which should be the same as the data we encrypted to begin with
                action new0 <= retData.first(); retData.deq(); endaction
                action new1 <= retData.first(); retData.deq(); endaction
                action new2 <= retData.first(); retData.deq(); endaction
                action new3 <= retData.first(); retData.deq(); endaction

                action
                   if ((new0 != data[127:96]) || (new1 != data[95:64]) || 
                       (new2 != data[63:32])  || (new3 != data[31:0]) ) begin
                      $display("ERROR: mismatch");
                      $display("       wanted %08x %08x %08x %08x", data[127:96], data[95:64], data[63:32], data[31:0] );
                      $display("       got    %08x %08x %08x %08x", new0, new1, new2, new3);
                      errorCnt <= errorCnt + 1;
                   end
                   else begin
                      matchCnt <= matchCnt + 1;

                      if ((matchCnt[3:0] == 0) && (matchCnt != 0))
                         $display("%d matches so far...", matchCnt);

                   end
                endaction
             endseq;
   endfunction

   ////////////////////////////////////////////////////////////////////////////////
   ////////////////////////////////////////////////////////////////////////////////
   ////////////////////////////////////////////////////////////////////////////////
   ////////////////////////////////////////////////////////////////////////////////
   Stmt test_input =  seq

                         ///////////////////////////////////////////////////////
                         // loop through all the cases we generated externally
                         for (ii<=0; ii != 255; ii<=ii+1) 
                            test( keyFile128.sub(ii), datFile.sub(ii) );

                         ///////////////////////////////////////////////////////
                         // what about 192 and 256 cases?
                         /*
                         for (ii<=0; ii != 255; ii<=ii+1) 
                            test( keyFile192.sub(ii), datFile.sub(ii) );

                         for (ii<=0; ii != 255; ii<=ii+1) 
                            test( keyFile256.sub(ii), datFile.sub(ii) );
                         */
                         
                         ///////////////////////////////////////////////////////
                         // wait for things to settle down
                         ii <= 0;
                         while ( ii < 32 ) action
                            if (aes.busy()) ii <= 0;
                            else            ii <= ii + 1;
                         endaction

                         noAction;
                         noAction;
                         noAction;
                         noAction;
                         noAction;

                         $display("Test Done!");
                         $finish(0);
                      endseq;

   mkAutoFSM(test_input);

   rule getOutput;
      TBus ddd <- aes.dbus.pop();
      case (ddd) matches
          tagged AesReturn {.data}: retData.enq(data);
         default: $display("ERROR: unknown data returned");
      endcase
   endrule

endmodule
