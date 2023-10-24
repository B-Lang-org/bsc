// This version uses the current FixedPoint library
import FixedPoint::*;

Bool debug = False;

typedef  2 INT_N;
typedef 15 FRA_N;

typedef  3 INT_D;
typedef 15 FRA_D;

typedef  2 INT_Q;
typedef 17 FRA_Q;


typedef 18 INT_EX; // 3 + FRA_D

typedef PipeFragment#(Tuple2#(FixedPoint#(int_n,fra_n),
                              FixedPoint#(int_d,fra_d)),
                      FixedPoint#(int_q,fra_q))
   Divide#(numeric type int_n,
           numeric type fra_n,
           numeric type int_d,
           numeric type fra_d,
           numeric type int_q,
           numeric type fra_q);
        //args: dividend,divisor (num,denom)
// Assume:
//   1 <= INT_D <= 2;

module mkDivide( Divide#(int_n, fra_n, int_d, fra_d, int_q, fra_q))
   provisos (Add#(3, fra_d, int_ex)

            // The table is size #(2,21)
            ,Add#(a__, fra_q, 21)
            ,Add#(b__, int_q, 2)

            // We truncate the multiply result to #(3,21) which
            // means that int_ex must be at least 1
            ,Add#(c__, 1, int_ex)

            // Resulting from fxptDivide of #(int_n,fra_n) and #(int_d,fra_d)
            ,Add#(d__, int_q, TAdd#(int_n, fra_d))
            ,Add#(int_n, fra_n, TAdd#(int_d, e__))

            // The Arith class provisos required this
            // XXX it should be solvable based on the above provisos
            ,Add#(6, TAdd#(fra_d, fra_d), TAdd#(int_ex, int_ex))

            // FixedPoint integer component must have non-zero width
            ,Min#(int_n, 1, 1)
            ,Min#(int_d, 1, 1)
            ,Min#(int_q, 1, 1)
            );

   Reg#(Maybe#(Tuple2#(FixedPoint#(int_ex, fra_n),
                       FixedPoint#(3,fra_d))))  buf1 <- mkReg(tagged Invalid);

   Reg#(Maybe#(Tuple3#(FixedPoint#(int_ex, fra_n),
                       FixedPoint#(3, fra_d),
                       FixedPoint#(2, FRAC_TABLE)))) buf2 <- mkReg(tagged Invalid);

   Reg#(Maybe#(Tuple2#(FixedPoint#(3,FRAC_TABLE),
                       FixedPoint#(2, FRAC_TABLE)))) buf3 <- mkReg(tagged Invalid);

   Reg#(Maybe#(FixedPoint#(2,FRAC_TABLE)))           buf4 <- mkReg(tagged Invalid);

   // Temporary registers for testing:
   Reg#(FixedPoint#(2, FRAC_TABLE)) max_x <- mkReg(0);
   Reg#(FixedPoint#(2, FRAC_TABLE)) min_x <- mkReg(fromRational(3,2));

   let fradv = valueOf(fra_d); // i.e. index of the digit to the left of the point.
   let fractv = valueOf(FRAC_TABLE); // i.e. index of the digit to the left of the point.

   // Temporary delay-line, for debugging:
   DLifc#(Tuple3#(FixedPoint#(int_n,fra_n),
                  FixedPoint#(int_d,fra_d),
                  FixedPoint#(int_q,fra_n))) qdl <- mkDelayLine(3);

   method ActionValue#(Maybe#(FixedPoint#(int_q,fra_q)))
          exec (Maybe#(Tuple2#(FixedPoint#(int_n,fra_n),
                               FixedPoint#(int_d,fra_d))) args);
      let qq = tagged Invalid;

      // Stage 0:
      // This stage normalises the denominator so that 1<=d<2; it also
      // shifts the numerator similarly.  We pass both to the next stage.
      case (args) matches
         tagged Invalid: begin
            buf1 <= tagged Invalid;
            qq <- qdl.exec(tagged Invalid);
         end
         tagged Valid {.num0, .denom0}:
            begin
               FixedPoint#(int_q, fra_n) q = (denom0==0 ? 0 : fxptDivide(num0,denom0));
               qq <- qdl.exec(tagged Valid tuple3(num0,denom0,q));
               FixedPoint#(int_ex, fra_n) num = adjust(num0);
               FixedPoint#(3,fra_d) denom = adjust(denom0);
               let b = fradv; // i.e. index of the digit to the left of the point.

               let n = pack(num);
               let d = pack(denom);

               // assume fra_d < 32 (could be made parametric):
               if (d[b:(b-15)] == 16'h0) begin
                  d = d << 16;
                  n = n << 16;
               end
               if (d[b:(b-7)] == 8'h0) begin
                  d = d << 8;
                  n = n << 8;
               end
               if (d[b:(b-3)] == 4'h0) begin
                  d = d << 4;
                  n = n << 4;
               end
               if (d[b:(b-1)] == 2'h0) begin
                  d = d << 2;
                  n = n << 2;
               end
               if (d[b] == 1'h0) begin
                  d = d << 1;
                  n = n << 1;
               end

               num = unpack(n);
               denom = unpack(d);
               buf1 <= tagged Valid tuple2(num,denom);
               if (debug)
                  begin
                     $write("num = "); fxptWrite(7, num0);
                     $write(" (%d), denom = ", num0); fxptWrite(7, denom0);
                     $display(" (%d)", denom0);
                     $write("num_n = "); fxptWrite(7, num);
                     $write(", denom_n = "); fxptWrite(7, denom); $display();
                  end
            end
      endcase

      //Stage 1:
      case (buf1) matches
         tagged Invalid: buf2 <= tagged Invalid;
         tagged Valid {.num, .denom}:
            begin
               if (denom==1)
                  begin
                     let two = 2 - unpack(1);
                     buf2 <= tagged Valid tuple3(-(num<<1),two,fromRational(1,2));
                  end
               else
                  begin
                     // Now we know denom>1.

                     // We form r(a) and r'(a), where a = 1+x, d = 1+x+y.
                     // Then r1 = r(a) + y*r'(a); (first two terms of Taylor series)
                     Tab_Index_Type i = pack(denom)[fradv-1:fradv-6];
                     FixedPoint#(2,fra_d) y = unpack(pack(denom)[fradv-7:0]);

                     let r = recip(i);
                     let r_prime = deriv(i);
                     FixedPoint#(2,FRAC_TABLE) r1 = r - fxptTruncate(fxptMult(y, r_prime));
                     // note: table gave -deriv

                     // Since 1<denom<=2, we should have 0.5<=r<1.  If r1 is
                     // too small, make it 0.5:
                     if (pack(r1)[fractv-1]!=1) r1 = fromRational(1,2);
                     buf2 <= tagged Valid tuple3(-num,denom,r1);
                     if (debug)
                        begin
                           $write("num_n = "); fxptWrite(7, num);
                           $write(", denom_n = "); fxptWrite(7, denom);
                           $write(", r1 = "); fxptWrite(7, r1); $display();
                        end
                  end
            end
      endcase

      //Stage 2:
      case (buf2) matches
         tagged Invalid: buf3 <= tagged Invalid;
         tagged Valid {.num, .denom, .r1}:
            begin
               // We know 0.5 <= r1 < 1.0
               FixedPoint#(2,FRAC_TABLE) r = unpack({3'b001,pack(r1)[fractv-2:0]});
               FixedPoint#(2, fra_d) d = unpack({2'b01,pack(denom)[fradv-1:0]});


               // We form q1 = n*r1, x1 = d*r1 (= 1 + e)
               FixedPoint#(3,FRAC_TABLE) q1 = fxptTruncate(fxptMult(num, r));
               FixedPoint#(2,FRAC_TABLE) x1 = fxptTruncate(fxptMult(d, r));

               if (x1>max_x)
                  begin
                     max_x <= x1;
                     $display("XXX max_x = %b", x1);
                  end
               if (x1<min_x)
                  begin
                     min_x <= x1;
                     $display("XXX min_x = %b", x1);
                  end

               buf3 <= tagged Valid tuple2(q1,x1);
               if (debug)
                  begin
                     $write("NUMR = %b ",pack(num)); fxptWrite(7, num); $display(" (%d)",num);
                     $write("DENOMR = %b ", pack(denom)); fxptWrite(7, denom);
                     $display(" (%d)",denom);
                     $write("r1 = %b ",pack(r1)); fxptWrite(7, r1); $display(" (%d)",r1);
                     $write("q1 = %b ",pack(q1)); fxptWrite(7, q1);
                     $write(", x1 = %b ",pack(x1)); fxptWrite(7, x1); $display();
                     $display("----");
                  end
            end
      endcase

      //Stage 3:
      case (buf3) matches
         tagged Invalid: buf4 <= tagged Invalid;
         tagged Valid {.q1, .x1}:
            begin
               // Since x1 = 1 + e, w = x1 - 2 = e - 1
               // So w*x1 = e^1 - 1, which is nearer -1.
               // We form q2 = w*q1, x2 = w*x1.
               // TEXF3 w = adjust(x1) - 2;
               // Faster (I hope):
               FixedPoint#(2,FRAC_TABLE) w = unpack({1'b1, pack(x1)[fractv:0]});
               FixedPoint#(2,FRAC_TABLE) q2 = fxptTruncate(fxptMult(w, q1));
               let x = fxptMult(w, x1);
               FixedPoint#(2,FRAC_TABLE) x2 = fxptTruncate(x);
               buf4 <= tagged Valid q2;
               if (debug &&& qq matches tagged Valid {.n,.d,.q})
                  begin
                     $write("NUM = "); fxptWrite(7, n);
                     $write(" (%d), DENOM = ", n); fxptWrite(7, d);
                     $display(" (%d)", d);
                     $write("x1 = %b ",pack(x1)); fxptWrite(7, x1);
                     $write(", w = %b ",pack(w)); fxptWrite(7, w); $display();
                     $write("x = %b ",pack(x)); fxptWrite(7, x); $display();
                     $write("q  =  %b ", pack(q)); fxptWrite(7, q); $display();
                     $write("q2 = %b ", pack(q2)); fxptWrite(7, q2);
                     $write(", x2 = %b ",pack(x2)); fxptWrite(7, x2); $display();
                     $display("----");
                  end
            end
      endcase

      // Final stage:
      case (buf4) matches
         tagged Invalid: return tagged Invalid;
         tagged Valid .q3: return tagged Valid dropMSBs(dropLSBs(q3));
      endcase
   endmethod
endmodule

// ----------------------------------------------------------------------

interface PipeFragment#(type in, type out);
   method ActionValue#(Maybe#(out)) exec(Maybe#(in) x);
endinterface

typedef PipeFragment#(t,t) DLifc#(type t);

// A module to provide a delay line to go in parallel with an actionvalue
// function call which introduces a delay:
module mkDelayLine#(Integer delay)(DLifc#(t))
   provisos (Bits#(t,st));
   Reg#(Maybe#(t)) rs[delay];

   for (Integer i=0; i<delay; i=i+1)
      rs[i] <- mkReg(tagged Invalid);

   method ActionValue#(Maybe#(t)) exec(Maybe#(t) mx);
      rs[0] <= mx;
      for (Integer i=1; i<delay; i=i+1)
         rs[i] <= rs[i-1];
      return rs[delay-1];
   endmethod
endmodule

// ----------------------------------------------------------------------

// Reduce the fractional bits of a fixed point value, discarding
// the low bits without rounding.
function FixedPoint#(i,rf) dropLSBs(FixedPoint#(i,f) a)
   provisos(Add#(_1,rf,f), Add#(i,f,TAdd#(i,f)),
            Add#(i,rf,TAdd#(i,rf)));
   Bit#(f) bits = a.f;
   Bit#(rf) out = bits[valueOf(f)-1 : valueOf(f)-valueOf(rf)];
   return FixedPoint { i:a.i, f: out };
endfunction: dropLSBs

// Reduce the integer size of a fixed point value, truncating
function FixedPoint#(ri,f) dropMSBs(FixedPoint#(i,f) a)
   provisos(Add#(_,TAdd#(ri,f),TAdd#(i,f)));
   return unpack(truncate(pack(a)));
endfunction: dropMSBs

// Fixed-point division.  The return type must have enough integer bits to
// contain the result of the division, or else the return value is undefined.
function FixedPoint#(ri,nf) fxptDivide(FixedPoint#(ni,nf) num,
                                       FixedPoint#(di,df) denom)
   provisos(
      // define the sizes "sz", "sz2", and "sz3" to be used in the body
      Add#(ni,nf,sz), Add#(df,sz,sz2), Add#(ni,df,sz3)

      // this is needed, because "di" is not mentioned above
      // (it's saying that width of "denom" is LTE width of "num")
      ,Add#(_1, TAdd#(di,df), sz2)
      // this is needed, because "ri" is not mentioned above
      // (the result int component must be LTE "sz3" == ni+df)
      ,Add#(_2,ri,sz3)

      // this can be figured out from the first three Add provisos
      ,Add#(sz3, nf, sz2)
   );
   Int#(sz2) n = unpack(signExtend(pack(num))) << valueOf(df);
   Int#(sz2) d = unpack(signExtend(pack(denom)));
   Int#(sz2) q = n / d;
   FixedPoint#(sz3,nf) out = unpack(pack(q));
   return dropMSBs(out);
endfunction: fxptDivide

// Adjust both ends of a fixed point value
function FixedPoint#(ri,rf) adjust(FixedPoint#(ai,af) a)
   provisos(Add#(ai,af,a_sz), Add#(ri,rf,r_sz), Add#(ri,rf,TAdd#(ri,rf)),
            Add#(ai,ri,ki), Add#(af,rf,kf));
   let base = pack(a);
   Bit#(ai) int_part = base[valueOf(a_sz)-1 : valueOf(af)];
   Bit#(af) frac_part = base[valueOf(af)-1 : 0];
   Bit#(ki) int_out = signExtend(int_part);
   Bit#(kf) frac_out = {frac_part, '0};
   Bit#(ri) i = int_out[valueOf(ri)-1 : 0];
   Bit#(rf) f = frac_out[valueOf(kf)-1 : valueOf(kf) - valueOf(rf)];
   return unpack({i,f});
endfunction: adjust

// ----------------------------------------------------------------------

typedef 21 FRAC_TABLE;
Integer tab_size = 64;
typedef  Bit#(6) Tab_Index_Type;
typedef FixedPoint#(2,FRAC_TABLE) Table_Type;

function Table_Type[] tables(Bool isRecip);
   Table_Type recip_t[tab_size];
   Table_Type deriv_t[tab_size];
   FixedPoint#(10,FRAC_TABLE) one = 1;
   FixedPoint#(10,FRAC_TABLE) del = fromRational(1,tab_size);
   FixedPoint#(10,FRAC_TABLE) d = one;

   for(Integer i=0; i<tab_size; i=i+1)
      begin
         let r = fxptDivide(one,d);
         d = d + del;
         recip_t[i] = r;
         deriv_t[i] = r*r;
      end
   return (isRecip ? recip_t : deriv_t);
endfunction

(* noinline *)
function Table_Type recip(Tab_Index_Type i);
   Table_Type recip_t[tab_size] = tables(True);
   return recip_t[i];
endfunction

(* noinline *)
function Table_Type deriv(Tab_Index_Type i);
   Table_Type deriv_t[tab_size] = tables(False);
   return deriv_t[i];
endfunction

// ----------------------------------------------------------------------

