import Defines::*;
import FIFOF::*;
import Vector::*;
import ProbeWire::*;

// import RegFile::*;
// import StmtFSM::*;

// don't use regfile versions
import RconComb::*;
import SboxComb::*;
import InvSboxComb::*;

interface Aes;
   interface DBus dbus;
   method Bool busy();
endinterface

// these are the state "names"
typedef enum {Wait, 
              KeyExpansionInit,   KeyExpansionLoop, 
              AddRoundKeyEncrypt, AddRoundKeyEncryptLoop, AddRoundKeyEncryptDone,
              AddRoundKeyDecrypt, AddRoundKeyDecryptLoop, AddRoundKeyDecryptDone,
              ReturnData } TState deriving(Bits, Eq);

(* synthesize *)
(* options = "-aggressive-conditions" *)
module mkAes( Aes );

   // TODO: make these actual ROMs
   // ROM tables, instant look up right now
   SboxRom sbox0 <- mkSboxRom; 
   SboxRom sbox1 <- mkSboxRom;
   SboxRom sbox2 <- mkSboxRom;
   SboxRom sbox3 <- mkSboxRom;
   SboxRom sbox4 <- mkSboxRom;
   SboxRom sbox5 <- mkSboxRom;
   SboxRom sbox6 <- mkSboxRom;
   SboxRom sbox7 <- mkSboxRom;
   SboxRom sbox8 <- mkSboxRom;
   SboxRom sbox9 <- mkSboxRom;
   SboxRom sbox10 <- mkSboxRom;
   SboxRom sbox11 <- mkSboxRom;
   SboxRom sbox12 <- mkSboxRom;
   SboxRom sbox13 <- mkSboxRom;
   SboxRom sbox14 <- mkSboxRom;
   SboxRom sbox15 <- mkSboxRom;

   InvSboxRom invsbox0 <- mkInvSboxRom;
   InvSboxRom invsbox1 <- mkInvSboxRom;
   InvSboxRom invsbox2 <- mkInvSboxRom;
   InvSboxRom invsbox3 <- mkInvSboxRom;
   InvSboxRom invsbox4 <- mkInvSboxRom;
   InvSboxRom invsbox5 <- mkInvSboxRom;
   InvSboxRom invsbox6 <- mkInvSboxRom;
   InvSboxRom invsbox7 <- mkInvSboxRom;
   InvSboxRom invsbox8 <- mkInvSboxRom;
   InvSboxRom invsbox9 <- mkInvSboxRom;
   InvSboxRom invsbox10 <- mkInvSboxRom;
   InvSboxRom invsbox11 <- mkInvSboxRom;
   InvSboxRom invsbox12 <- mkInvSboxRom;
   InvSboxRom invsbox13 <- mkInvSboxRom;
   InvSboxRom invsbox14 <- mkInvSboxRom;
   InvSboxRom invsbox15 <- mkInvSboxRom;

   RconRom rcon <- mkRconRom;

   // input fifos
   FIFOF#(TBus) inQ  <- mkSizedFIFOF(2);
   FIFOF#(TBus) outQ <- mkSizedFIFOF(2);

   // internal register and busses
   Vector#(60,Reg#(UWORD)) w    <- replicateM(mkRegU);
   Reg#(VBytes) data            <- mkRegU;

   Reg#(Bool) verbose <- mkReg(False);

   ///////////////////////////////////////////////////////////////
   // macro definitions
   function UBYTE xtime( UBYTE a );
      return ((a & 'h80)!=0) ? ((a<<1) ^ 8'h1B) : (a<<1);
   endfunction
   
   function UWORD rotWord( UWORD word );
      // return truncate(word << 24) | (word >> 24);
      // return { word[7:0] , word[31:8] };
      return { word[23:0], word[31:24] };
   endfunction
   
   function UWORD sWord1( UWORD word );
      return {sbox0.read( word[31:24] ), sbox2.read( word[23:16] ),
              sbox1.read( word[15:8] ),  sbox3.read( word[7:0] )};
   endfunction
   
   function UWORD sWord2( UWORD word );
      return {sbox4.read( word[31:24] ), sbox6.read( word[23:16] ),
              sbox5.read( word[15:8] ),  sbox7.read( word[7:0] )};
   endfunction
   
   function UWORD sWord3( UWORD word );
      return {sbox8.read( word[31:24] ), sbox10.read( word[23:16] ),
              sbox9.read( word[15:8] ), sbox11.read( word[7:0] )};
   endfunction
   
   function UWORD sWord4( UWORD word );
      return {sbox12.read( word[31:24] ), sbox13.read( word[23:16] ),
              sbox14.read( word[15:8] ),  sbox15.read( word[7:0] )};
   endfunction
   
   ///////////////////////////////////////////////////////////////
   function VBytes funcAddRoundKey( VBytes dt, Bit#(6) round_Nb );
      VBytes res = newVector;
      // VBytes res;
      
      Vector#(60,UWORD) ww = map(fromReg,w);

      UWORD w0 = ww[round_Nb];
      UWORD w1 = ww[round_Nb+1];
      UWORD w2 = ww[round_Nb+2];
      UWORD w3 = ww[round_Nb+3];

      // <= "register assign"
      // =  "wire assign"
      // <- "module/instance or action"
      // res[0]    = (dt[0]) ^ truncate(w0 >> 24); 

      res[0]    = dt[0]^ (w0[31:24]); 
      res[1]    = dt[1]^ (w0[23:16]);
      res[2]    = dt[2]^ (w0[15: 8]);
      res[3]    = dt[3]^ (w0[ 7: 0]);
      res[4]    = dt[4]^ (w1[31:24]); 
      res[5]    = dt[5]^ (w1[23:16]); 
      res[6]    = dt[6]^ (w1[15: 8]); 
      res[7]    = dt[7]^ (w1[ 7: 0]); 
      res[8]    = dt[8]^ (w2[31:24]); 
      res[9]    = dt[9]^ (w2[23:16]); 
      res[10]   = dt[10]^(w2[15: 8]); 
      res[11]   = dt[11]^(w2[ 7: 0]); 
      res[12]   = dt[12]^(w3[31:24]); 
      res[13]   = dt[13]^(w3[23:16]); 
      res[14]   = dt[14]^(w3[15: 8]); 
      res[15]   = dt[15]^(w3[ 7: 0]); 
      
      return res;
   endfunction

   function VBytes funcSubBytes( VBytes d );
      VBytes res = newVector;
      res[0]  = sbox0.read( d[0] );
      res[1]  = sbox1.read( d[5] );
      res[2]  = sbox2.read( d[10] );
      res[3]  = sbox3.read( d[15] );
      res[4]  = sbox4.read( d[4] );
      res[5]  = sbox5.read( d[9] );
      res[6]  = sbox6.read( d[14] );
      res[7]  = sbox7.read( d[3] );
      res[8]  = sbox8.read( d[8] );
      res[9]  = sbox9.read( d[13] );
      res[10] = sbox10.read( d[2] );
      res[11] = sbox11.read( d[7] );
      res[12] = sbox12.read( d[12] );
      res[13] = sbox13.read( d[1] );
      res[14] = sbox14.read( d[6] );
      res[15] = sbox15.read( d[11] );
      return res;
   endfunction
   
   function VBytes funcMixColumns( VBytes d );
      VBytes res = newVector;
      res[0] = xtime(d[0])           ^xtime(d[1])^d[1]  ^d[2]                   ^d[3];
      res[1] = d[0]                  ^xtime(d[1])           ^xtime(d[2])^d[2]   ^d[3];
      res[2] = d[0]                  ^d[1]                  ^xtime(d[2])            ^xtime(d[3])^d[3];
      res[3] = xtime(d[0])^d[0]      ^d[1]                  ^d[2]                   ^xtime(d[3]);
      res[4] = xtime(d[4])           ^xtime(d[5])^d[5] ^d[6]                    ^d[7];
      res[5] = d[4]                  ^xtime(d[5])          ^xtime(d[6])^d[6]    ^d[7];
      res[6] = d[4]                  ^d[5]                 ^xtime(d[6])             ^xtime(d[7])^d[7];
      res[7] = xtime(d[4])^d[4]  ^d[5]                 ^d[6]                    ^xtime(d[7]);
      res[8] = xtime(d[8])              ^xtime(d[9])^d[9]   ^d[10]                  ^d[11];
      res[9] = d[8]                     ^xtime(d[9])            ^xtime(d[10])^d[10] ^d[11];
      res[10] = d[8]                    ^d[9]                   ^xtime(d[10])           ^xtime(d[11])^d[11];
      res[11] = xtime(d[8])^d[8]    ^d[9]                   ^d[10]                  ^xtime(d[11]);
      res[12] = xtime(d[12])            ^xtime(d[13])^d[13] ^d[14]                  ^d[15];
      res[13] = d[12]                   ^xtime(d[13])           ^xtime(d[14])^d[14] ^d[15];
      res[14] = d[12]                   ^d[13]                  ^xtime(d[14])           ^xtime(d[15])^d[15];
      res[15] = xtime(d[12])^d[12]  ^d[13]                  ^d[14]                  ^xtime(d[15]);
      return res;
   endfunction

   //////////////////////////////////////////////////////////////
   function UBYTE mc_mul_e(UBYTE state);
      UBYTE two = xtime(state);
      UBYTE four = xtime(two);
      UBYTE eight = xtime(four);
      return eight^four^two;
   endfunction

   function UBYTE mc_mul_9(UBYTE state);
      UBYTE two = xtime(state);
      UBYTE four = xtime(two);
      UBYTE eight = xtime(four);
      return eight^state;
   endfunction

   function UBYTE mc_mul_d(UBYTE state);
      UBYTE two = xtime(state);
      UBYTE four = xtime(two);
      UBYTE eight = xtime(four);
      return eight^four^state;
   endfunction

   function UBYTE mc_mul_b(UBYTE state);
      UBYTE two = xtime(state);
      UBYTE four = xtime(two);
      UBYTE eight = xtime(four);
      return eight^two^state;
   endfunction

   function VBytes funcInvMixColumns( VBytes d );
      // VBytes is a "Vector"
      // VBytes temp = ?;             // COMPILER with run for a long time!!!! ERROR!
      // VBytes temp = replicate(?);  // this is good
      // VBytes temp = newVector;     // same as replicate(?)

      VBytes temp = newVector;
      VBytes res  = newVector;

      // loop 0,1,2,3
      for (Integer i=0; i<4; i=i+1) begin
         temp[0]  = mc_mul_e(d[4*i+0]);
         temp[1]  = mc_mul_b(d[4*i+1]);
         temp[2]  = mc_mul_d(d[4*i+2]);
         temp[3]  = mc_mul_9(d[4*i+3]);
         temp[4]  = mc_mul_9(d[4*i+0]);
         temp[5]  = mc_mul_e(d[4*i+1]);
         temp[6]  = mc_mul_b(d[4*i+2]);
         temp[7]  = mc_mul_d(d[4*i+3]);
         temp[8]  = mc_mul_d(d[4*i+0]);
         temp[9]  = mc_mul_9(d[4*i+1]);
         temp[10] = mc_mul_e(d[4*i+2]);
         temp[11] = mc_mul_b(d[4*i+3]);
         temp[12] = mc_mul_b(d[4*i+0]);
         temp[13] = mc_mul_d(d[4*i+1]);
         temp[14] = mc_mul_9(d[4*i+2]);
         temp[15] = mc_mul_e(d[4*i+3]);
         res[4*i+0] = temp[0]^temp[1]^temp[2]^temp[3];
         res[4*i+1] = temp[4]^temp[5]^temp[6]^temp[7];
         res[4*i+2] = temp[8]^temp[9]^temp[10]^temp[11];
         res[4*i+3] = temp[12]^temp[13]^temp[14]^temp[15];
      end
      return res;
   endfunction

   function VBytes funcInvShiftRow( VBytes d );
      VBytes res = newVector;
      res[0]  = invsbox0.read(d[0]);
      res[1]  = invsbox13.read(d[13]);
      res[2]  = invsbox10.read(d[10]);
      res[3]  = invsbox7.read(d[7]);
      res[4]  = invsbox4.read(d[4]);
      res[5]  = invsbox1.read(d[1]);
      res[6]  = invsbox14.read(d[14]);
      res[7]  = invsbox11.read(d[11]);
      res[8]  = invsbox8.read(d[8]);
      res[9]  = invsbox5.read(d[5]);
      res[10] = invsbox2.read(d[2]);
      res[11] = invsbox15.read(d[15]);
      res[12] = invsbox12.read(d[12]);
      res[13] = invsbox9.read(d[9]);
      res[14] = invsbox6.read(d[6]);
      res[15] = invsbox3.read(d[3]);
      return res;
   endfunction

   ////////////////////////////////////////////////
   // for Encrypt128
   // input: Key3, Key2, Key1, Key0, PlainText3, PlainText2, PlainText1, PlainText0 
   //    do encryption
   // output: CipherText3, CipherText2, CipherText1, CipherText0

   //////////////////////////////////////////////////////////////////////
   //////////////////////////////////////////////////////////////////////   
   Reg#(Bit#(6))    nk <- mkReg(0);
   Reg#(Bit#(6))    nr <- mkReg(0);
   Reg#(Bit#(6)) iWord <- mkRegU;

   Reg#(Bit#(4)) i <- mkReg(0);
   Reg#(Bit#(6)) m <- mkReg(0);

   Reg#(Bit#(6)) j  <- mkReg(0);
   Reg#(Bit#(6)) tk <- mkReg(0);
   Reg#(Bool) nk4  <- mkReg(False);
   Reg#(Bool) nk6  <- mkReg(False);
   Reg#(Bool) nk8  <- mkReg(False);

   Reg#(UWORD) temp <- mkReg(0);
   Reg#(UWORD) temp0 <- mkReg(0);

   Reg#(Bool) tmp4 <- mkReg(False);
   Reg#(Bool) tmp6 <- mkReg(False);
   Reg#(Bool) tmp8 <- mkReg(False);
            
   Reg#(UWORD) temp1 <- mkReg(0);
   Reg#(UWORD) temp2 <- mkReg(0);
   Reg#(UWORD) temp3 <- mkReg(0);
   Reg#(UWORD) temp4 <- mkReg(0);

   Reg#(Bit#(3)) dataCntr <- mkReg(4);

   ////////////////////////////////////////////////////////////
   ////////////////////////////////////////////////////////////
   function UWORD getBusData ( TBus d );
      case (d) matches
         tagged Encrypt128 {.dt}: return dt;
         tagged Encrypt192 {.dt}: return dt;
         tagged Encrypt256 {.dt}: return dt;
         tagged Decrypt128 {.dt}: return dt;
         tagged Decrypt192 {.dt}: return dt;
         tagged Decrypt256 {.dt}: return dt;
         default: return ?;
         // $display("ERROR: bad bus data");
      endcase
   endfunction

   ////////////////////////////////////////////////////////////////////////////////
   ////////////////////////////////////////////////////////////////////////////////
   ////////////////////////////////////////////////////////////////////////////////
   ////////////////////////////////////////////////////////////////////////////////
   Reg#(TState)  state <- mkReg(Wait);
   Reg#(Bit#(6)) wcntr <- mkReg(0);

   // True  = do Encrypt
   // False = do Decrypt
   Reg#(Bool)  encrypt <- mkReg(True);

   ///////////////////////////////////////////////////////////////
   // wait for Encrypt or Decrypt command from AHB
   rule stateWait (state == Wait);
      
      for (Integer i=1; i<60; i=i+1)
         (w[i]) <= 0;

      // wait for the first word at the head of the fifo
      case (inQ.first) matches
         tagged Encrypt128 {.dt}: begin 
            nk <= 4; 
            nr <= 10; 
            (w[0]) <= dt; 
            encrypt <= True;
            state <= KeyExpansionInit;
         end
         tagged Decrypt128 {.dt}: begin 
            nk <= 4; 
            nr <= 10; 
            (w[0]) <= dt; 
            encrypt <= False;
            state <= KeyExpansionInit;
         end
         tagged Encrypt192 {.dt}: begin 
            nk <= 6; 
            nr <= 12; 
            (w[0]) <= dt; 
            encrypt <= True;
            state <= KeyExpansionInit;
         end
         tagged Decrypt192 {.dt}: begin 
            nk <= 6; 
            nr <= 12; 
            (w[0]) <= dt; 
            encrypt <= False;
            state <= KeyExpansionInit;
         end
         tagged Encrypt256 {.dt}: begin 
            nk <= 8; 
            nr <= 14; 
            (w[0]) <= dt; 
            encrypt <= True;
            state <= KeyExpansionInit;
         end
         tagged Decrypt256 {.dt}: begin 
            nk <= 8; 
            nr <= 14; 
            (w[0]) <= dt; 
            encrypt <= False;
            state <= KeyExpansionInit;
         end
         // default: // TODO what do we do if there is a bad packet?
      endcase

      wcntr <= 1;
      inQ.deq();
   endrule

   ///////////////////////////////////////////////////////////////
   rule stateKeyExpansionInit (state == KeyExpansionInit);
      let key = getBusData( inQ.first() );
      inQ.deq();

      // get w[1], w[2], w[3] (and maybe, 4,5 and 6,7)
      (w[wcntr]) <= key;
      wcntr <= wcntr + 1;

      if ((wcntr+1) == nk) begin
         i <= 0;
         m <= 0;
         nk4   <= (nk == 4);
         nk6   <= (nk == 6);
         nk8   <= (nk == 8);
         case (nk[3:0])
            'h4: begin
                    j     <= 4;
                    tk    <= 44;
                    temp0 <= fromReg(w[0]);
                    temp  <= key; // fromReg(w[3]);
                 end
            
            'h6: begin
                    j      <= 6; 
                    tk     <= 52;
                    temp0  <= fromReg(w[0]);
                    temp   <= key; // fromReg(w[5]);
                 end
            
            'h8: begin
                    j     <= 8;
                    tk    <= 60;
                    temp0 <= fromReg(w[0]);
                    temp  <= key; // fromReg(w[7]);
                 end
         endcase
         dataCntr <= 0;
         state <= KeyExpansionLoop;
      end
   endrule

   ///////////////////////////////////////////////////////////////
   rule getData ((state == KeyExpansionLoop) && (dataCntr < 4));
      UWORD word = getBusData( inQ.first() );
      VBytes nData = data;
      
      // nData 15 14 13 12 11 10 ...... 03 02 01 00
      //                                15 16 7e 2b
      
      case (dataCntr)
         0: begin nData[0]=word[31:24];  nData[1]=word[23:16];   nData[2]=word[15:8];  nData[3]=word[7:0]; end 
         1: begin nData[4]=word[31:24];  nData[5]=word[23:16];   nData[6]=word[15:8];  nData[7]=word[7:0]; end 
         2: begin nData[8]=word[31:24];  nData[9]=word[23:16];   nData[10]=word[15:8]; nData[11]=word[7:0]; end 
         3: begin nData[12]=word[31:24]; nData[13]=word[23:16];  nData[14]=word[15:8]; nData[15]=word[7:0]; end 
      endcase

      data     <= nData;
      dataCntr <= dataCntr + 1;
      inQ.deq();
   endrule
   
   ///////////////////////////////////////////////////////////////
   // wait for Encrypt or Decrypt command from AHB
   // TODO: do two of these in one cycle!
   rule stateKeyExpansionLoop (state == KeyExpansionLoop);
      UWORD ind = ?;
      UWORD wmPlus1 = fromReg( select( w, m+1 ) ); // same as w[m+1]
      
      // since these happen in parallel, it looks like they happen here
      Bool tmp4 = (j==4||j==8 ||j==12||j==16||j==20||j==24||j==28||j==32||j==36||j==40||j==44||j==52);
      Bool tmp6 = (j==6||j==12||j==18||j==24||j==30||j==36||j==42||j==48);
      Bool tmp8 = (j==8||j==16||j==24||j==32||j==40||j==48||j==56);
      
      UWORD temp1 = temp          ^ temp0;
      UWORD temp2 = sWord2(temp)  ^ temp0;
      UWORD temp3 = rotWord(temp);
      UWORD temp4 = rcon.read(i)  ^ temp0; // rcon[i]
      
      if( (nk4 && tmp4) || (nk6 && tmp6) || (nk8 && tmp8) ) begin
         //$display("temp %08x %08x", ind, wmPlus1);
         //$display("     %08x %08x %08x %08x", temp1, temp2, temp3, temp4);
         //$display("     %08x %08x", temp, temp0);
         //$display("     %08x %08x", sWord1(temp3), temp4);
         //$display("     %08x", rcon.read(i));
         
         (w[j]) <= sWord1(temp3) ^ temp4;
         temp   <= sWord1(temp3) ^ temp4;
         temp0 <= wmPlus1;
         i     <= i + 1;
      end
      
      else if (nk8 && tmp4) begin
         (w[j]) <= temp2;
         temp   <= temp2; //temp = w[j] 
         temp0  <= wmPlus1;
      end
      
      else begin
         (w[j]) <= temp1;
         temp  <= temp1; //temp = w[j]
         temp0 <= wmPlus1;
      end

      m <= m + 1;

      // execute this state of the statemachine 44 or 52 or 60 times
      if ((j+1) == tk) begin
         j <= 0;
         if (encrypt)
            state <= AddRoundKeyEncrypt;
         else
            state <= AddRoundKeyDecrypt;
      end
      else
         j <= j + 1;

   endrule

   ////////////////////////////////////////////////////////////
   Reg#(Bit#(6)) round <- mkReg(0);
   rule stateAddRoundKeyEncrypt (state == AddRoundKeyEncrypt);
      VBytes d1 = funcAddRoundKey( data ,  0);
      
      data  <= d1;
      round <= 1;
      state <= AddRoundKeyEncryptLoop;
   endrule
   
   ////////////////////////////////////////////////////////////
   // loop 1..nr
   Wire#(VBytes) encrypt_d2 <- mkProbeWire;
   Wire#(VBytes) encrypt_d3 <- mkProbeWire;

   rule stateAddRoundKeyEncryptLoop (state == AddRoundKeyEncryptLoop);
      rule step1;
         encrypt_d2 <= funcSubBytes( data );
      endrule
   
      rule step2;
         encrypt_d3 <= funcMixColumns( encrypt_d2 );
      endrule
   
      rule step3;
         data  <= funcAddRoundKey( encrypt_d3, round * 4 );
         round <= round + 1;
         if ((round+1) == nr)
            state <= AddRoundKeyEncryptDone;
      endrule
   endrule

   ////////////////////////////////////////////////////////////
   Wire#(VBytes) encrypt_done_d2 <- mkProbeWire;
   rule stateAddRoundKeyEncryptDone (state == AddRoundKeyEncryptDone);
   
      rule step1;
         encrypt_done_d2 <= funcSubBytes( data );
      endrule
   
      rule step2;
         VBytes d1 = funcAddRoundKey( encrypt_done_d2, round * 4 );
         data <= d1;
         state <= ReturnData;
         
         if (verbose) begin
            $display("DBG: roundKey = %02x%02x%02x%02x", d1[0], d1[4], d1[8],  d1[12]);
            $display("DBG: roundKey = %02x%02x%02x%02x", d1[1], d1[5], d1[9],  d1[13]);
            $display("DBG: roundKey = %02x%02x%02x%02x", d1[2], d1[6], d1[10], d1[14]);
            $display("DBG: roundKey = %02x%02x%02x%02x", d1[3], d1[7], d1[11], d1[15]);
         end
      endrule

   endrule

   ////////////////////////////////////////////////////////////
   ////////////////////////////////////////////////////////////
   rule stateAddRoundKeyDecrypt (state == AddRoundKeyDecrypt);
      VBytes d1 = funcAddRoundKey(data,  nr * 4);
      VBytes d2 = funcInvShiftRow(d1);
      data  <= d2;

      round <= nr - 1;
      state <= AddRoundKeyDecryptLoop;

      if (verbose) begin
         $display("DBG: roundKey = %02x%02x%02x%02x round=%x", d1[0], d1[4], d1[8],  d1[12], nr);
         $display("DBG: roundKey = %02x%02x%02x%02x", d1[1], d1[5], d1[9],  d1[13]);
         $display("DBG: roundKey = %02x%02x%02x%02x", d1[2], d1[6], d1[10], d1[14]);
         $display("DBG: roundKey = %02x%02x%02x%02x", d1[3], d1[7], d1[11], d1[15]);
         $display("DBG: invsrow  = %02x%02x%02x%02x", d2[0], d2[4], d2[8],  d2[12]);
         $display("DBG: invsrow  = %02x%02x%02x%02x", d2[1], d2[5], d2[9],  d2[13]);
         $display("DBG: invsrow  = %02x%02x%02x%02x", d2[2], d2[6], d2[10], d2[14]);
         $display("DBG: invsrow  = %02x%02x%02x%02x", d2[3], d2[7], d2[11], d2[15]);
      end
   endrule

   Wire#(VBytes) decrypt_d2 <- mkProbeWire;
   Wire#(VBytes) decrypt_d3 <- mkProbeWire;
   rule stateAddRoundKeyDecryptLoop (state == AddRoundKeyDecryptLoop);
      rule step1;
         VBytes d2 = funcAddRoundKey( data, round * 4 );
         decrypt_d2 <= d2;
         if (verbose) begin
            $display("DBG: roundKey = %02x%02x%02x%02x round=%x", d2[0], d2[4], d2[8],  d2[12], round);
            $display("DBG: roundKey = %02x%02x%02x%02x", d2[1], d2[5], d2[9],  d2[13]);
            $display("DBG: roundKey = %02x%02x%02x%02x", d2[2], d2[6], d2[10], d2[14]);
            $display("DBG: roundKey = %02x%02x%02x%02x", d2[3], d2[7], d2[11], d2[15]);
         end
      endrule
      
      rule step2 (state == AddRoundKeyDecryptLoop);
         VBytes d3 = funcInvMixColumns( decrypt_d2 );
         decrypt_d3 <= d3;
         if (verbose) begin
            $display("DBG: invmixcolumn = %02x%02x%02x%02x", d3[0], d3[4], d3[8],  d3[12]);
            $display("DBG: invmixcolumn = %02x%02x%02x%02x", d3[1], d3[5], d3[9],  d3[13]);
            $display("DBG: invmixcolumn = %02x%02x%02x%02x", d3[2], d3[6], d3[10], d3[14]);
            $display("DBG: invmixcolumn = %02x%02x%02x%02x", d3[3], d3[7], d3[11], d3[15]);
         end
      endrule
   
      rule step3 (state == AddRoundKeyDecryptLoop);
         VBytes d1 = funcInvShiftRow( decrypt_d3 );
         if (verbose) begin
            $display("DBG: roundKey = %02x%02x%02x%02x round=%x", d1[0], d1[4], d1[8],  d1[12], round+1);
            $display("DBG: roundKey = %02x%02x%02x%02x", d1[1], d1[5], d1[9],  d1[13]);
            $display("DBG: roundKey = %02x%02x%02x%02x", d1[2], d1[6], d1[10], d1[14]);
            $display("DBG: roundKey = %02x%02x%02x%02x", d1[3], d1[7], d1[11], d1[15]);
         end
         
         data <= d1;
         round <= round - 1;
         if (round == 1)
            state <= AddRoundKeyDecryptDone;
      endrule
   endrule

   ////////////////////////////////////////////////////////////
   rule stateAddRoundKeyDecryptDone (state == AddRoundKeyDecryptDone);
      VBytes d1 = funcAddRoundKey( data, 0 );
      data <= d1;
      state <= ReturnData;

      if (verbose) begin
         $display("DBG: roundKey = %02x%02x%02x%02x", d1[0], d1[4], d1[8],  d1[12]);
         $display("DBG: roundKey = %02x%02x%02x%02x", d1[1], d1[5], d1[9],  d1[13]);
         $display("DBG: roundKey = %02x%02x%02x%02x", d1[2], d1[6], d1[10], d1[14]);
         $display("DBG: roundKey = %02x%02x%02x%02x", d1[3], d1[7], d1[11], d1[15]);
      end
   endrule

   ////////////////////////////////////////////////////////////
   ////////////////////////////////////////////////////////////
   rule stateReturnData (state == ReturnData);
      if (verbose && (j==0)) begin
         for (Integer i=0; i<60; i=i+1)
            $display("w[%02d] => %08x", i, fromReg(w[i]));
      end

      // return result to AHB
      outQ.enq( AesReturn( {data[j*4+0], data[j*4+1], data[j*4+2], data[j*4+3] } ) );
      j <= j + 1;

      if ((j+1) == 4) begin
         // back to the beginning
         state <= Wait; 
      end
   endrule
   
   ////////////////////////////////////////////////
   interface DBus dbus = 
      interface DBus
         method Action push(TBus d);
            inQ.enq(d);
         endmethod
         
         method ActionValue#(TBus) pop();
            outQ.deq();
            return outQ.first();
         endmethod
      endinterface;
      
      method Bool busy();
         return inQ.notEmpty || outQ.notEmpty || (state != Wait);
      endmethod
         
endmodule
