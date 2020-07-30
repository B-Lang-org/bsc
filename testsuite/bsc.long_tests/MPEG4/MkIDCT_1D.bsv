//////////////////////////////////////////////////////////////////////////
/* 1D IDCT module. The input_data Int_width determines whether to
calculate row IDCT or column IDCT. Row IDCT and Column IDCT are
essentially the same except for the third and the last stage 
 */
//////////////////////////////////////////////////////////////////////////

package MkIDCT_1D;

import ConfigReg :: *;
import ArithModules :: *;
import PingPongBuffers :: *;
import TBuffer :: *;
import List :: *;


interface IDCT_1D_IFC#(type w_in, type w_out);
    method Action start (Int#(w_in) d_in, bit strb);
    method DataStrobe#(w_out) result();
endinterface : IDCT_1D_IFC

module mkIDCT_1D (IDCT_1D_IFC#(w_in, w_out)) provisos (Add#(w_in,xyz,16),
                  Add#(abc,w_out,16));
    
    Bool row = (valueOf(w_in) == 12);
    
    Reg#(Maybe#(Bit#(6))) stg1_cnt();
    mkConfigReg#(Nothing) the_stg1_cnt(stg1_cnt);
    Reg#(Maybe#(Bit#(3))) stg2_cnt();
    mkReg#(Nothing) the_stg2_cnt(stg2_cnt);
    Reg#(Maybe#(Bit#(3))) stg2_mult_cnt();
    mkReg#(Nothing) the_stg2_mult_cnt(stg2_mult_cnt);
    Reg#(Maybe#(Bit#(3))) stg3_cnt();
    mkReg#(Nothing) the_stg3_cnt(stg3_cnt);
    Reg#(Maybe#(Bit#(3))) stg4_cnt();
    mkReg#(Nothing) the_stg4_cnt(stg4_cnt);
    Reg#(Maybe#(Bit#(3))) stg5_cnt();
    mkReg#(Nothing) the_stg5_cnt(stg5_cnt);
    Reg#(Maybe#(Bit#(3))) stg6_cnt();
    mkReg#(Nothing) the_stg6_cnt(stg6_cnt);
    Reg#(Maybe#(Bit#(3))) stg7_cnt();
    mkReg#(Nothing) the_stg7_cnt(stg7_cnt);
    Reg#(Maybe#(Bit#(6))) out_cnt();
    mkReg#(Nothing) the_out_cnt(out_cnt);
    Reg#(Int#(16)) d_out();
    mkReg#(0) the_d_out(d_out);
    
    Pingpong_IFC#(16,8) stg1_data();
    pingpong_16_7 the_stg1_data(stg1_data);
    Pingpong_IFC#(32,7) stg2a_data();
    pingpong_32_6 the_stg2a_data(stg2a_data);
    Pingpong_IFC#(32,7) stg2b_data();
    pingpong_32_6 the_stg2b_data(stg2b_data);
    Pingpong_IFC#(32,8) stg3_data();
    pingpong_32_7 the_stg3_data(stg3_data);
    Pingpong_IFC#(32,8) stg4_data();
    pingpong_32_7 the_stg4_data(stg4_data);
    Pingpong_IFC#(32,8) stg5_data();
    pingpong_32_7 the_stg5_data(stg5_data);
    Pingpong_IFC#(32,8) stg6_data();
    pingpong_32_7 the_stg6_data(stg6_data);

    Mult_IFC#(16) mult1();
    mult_W1W2W3 the_mult1(mult1);
    Mult_IFC#(16) mult2();
    mult_W5W6W7 the_mult2(mult2);

    AddSub_IFC adder1();
    mkAddSub the_adder1(adder1);
    AddSub_IFC adder2();
    mkAddSub the_adder2(adder2);
    AddSub_IFC adder3();
    mkAddSub the_adder3(adder3);
    AddSub_IFC adder4();
    mkAddSub the_adder4(adder4);

    ConstMult_IFC mult181();
    mkConstMult the_mult181(mult181);

///////////////////////////////////////////////////////////////////////////////
/* The Controller for 1D-IDCT. Each stage has a counter, which
controls the data path for that particular stage. A value of "Nothing"
implies that stage is disabled. Each stage enables the counter for the
next stage as soon it completes all the necessary operations.
stg1_cnt shifts the incoming data into the first pingpong buffer.
stg2_cnt shifts the data from the first pingpong buffer into the
pipelined multiplier.  stg2_mult_cnt shifts the data from the
pipelined multiplier into the second pingpong buffer.  stg3_cnt shifts
the data from second pingpong buffer to the third pingpong buffer
after the necessary operations, and so on.  
 */
///////////////////////////////////////////////////////////////////////////////

   function Action cntUpdate( 
                             Reg#(Maybe#(Bit#(a1))) cnt1,
                             Reg#(Maybe#(Bit#(a2))) cnt2,
                             Bit#(3) value);
      Action act =
      action
         if ( cnt1 matches tagged Just { .x_cnt1 } &&&
                              ( x_cnt1[2:0] == value) )
           // restart counter because of max previous counter.
           begin
              cnt2 <= Just( 0 ) ;
           end
         else if ( cnt2 matches tagged Just { .x_cnt2 } &&&
                                   ( x_cnt2 < 7 ) )
           // update the counter
           begin
              cnt2 <= Just ( x_cnt2 + 1 ) ;
           end
         else
            // counter is at nothing
            cnt2 <= Nothing ;
      endaction ;
      return act;
   endfunction

   rule counterUpdate ;
         cntUpdate( stg1_cnt,      stg2_cnt,      6 ) ;
         cntUpdate( stg2_cnt,      stg2_mult_cnt, 1 ) ;
         cntUpdate( stg2_mult_cnt, stg3_cnt,      7 ) ;
         cntUpdate( stg3_cnt,      stg4_cnt,      7 ) ;
         cntUpdate( stg4_cnt,      stg5_cnt,      7 ) ;
         cntUpdate( stg5_cnt,      stg6_cnt,      7 ) ;
         cntUpdate( stg6_cnt,      stg7_cnt,      7 ) ;
   endrule

   // function which creates a rule, with
   // name _rule_name_, predicate cnt == Just(p) and body c
    function Rules cr (String rule_name,
                       Maybe#(Bit#(a)) cnt,
                       Bit#(a) p,
                       Action c);
       Rules r = rules
             rule cr_rule (cnt == Just (p));
                c;
             endrule
       endrules;
       return r;
    endfunction

////////////////////////////////////////////////////////////////////////////////
//Data Path flow (Each counter, see comments above, controls the data path)
///////////////////////////////////////////////////////////////////////////////

    Rules m01 = cr ("stage2_0a", stg2_cnt, 0, 
                    mult1.multiply (stg1_data.read[0], 2'b11));
    Rules m02 = cr ("stage2_0b", stg2_cnt, 0, 
                    mult2.multiply (stg1_data.read[1], 2'b10));
    Rules m03 = cr ("stage2_1a", stg2_cnt, 1, 
                    mult1.multiply (stg1_data.read[1], 0));
    Rules m04 = cr ("stage2_1b", stg2_cnt, 1,
                    mult2.multiply (stg1_data.read[2], 1));
    Rules m05 = cr ("stage2_2a", stg2_cnt, 2, 
                    mult1.multiply (stg1_data.read[2], 1));
    Rules m06 = cr ("stage2_2b", stg2_cnt, 2, 
                    mult2.multiply (stg1_data.read[3], 0));
    Rules m07 = cr ("stage2_3a", stg2_cnt, 3, 
                    mult1.multiply (stg1_data.read[3], 2'b10));
    Rules m08 = cr ("stage2_3b", stg2_cnt, 3, 
                    mult2.multiply (stg1_data.read[4], 2'b11));
    Rules m09 = cr ("stage2_4a", stg2_cnt, 4, 
                    mult1.multiply (stg1_data.read[5], 2'b10));
    Rules m10 = cr ("stage2_4b", stg2_cnt, 4, 
                    mult2.multiply (stg1_data.read[5], 0));
    Rules m11 = cr ("stage2_5a", stg2_cnt, 5, 
                    mult1.multiply (stg1_data.read[6], 1));
    Rules m12 = cr ("stage2_5b", stg2_cnt, 5, 
                    mult2.multiply (stg1_data.read[6], 1));
    Rules m13 = cr ("stage2_7a", stg2_cnt, 7, 
                    mult1.multiply (stg1_data.read[7], 0));
    Rules m14 = cr ("stage2_7a", stg2_cnt, 7, 
                    mult2.multiply (stg1_data.read[7], 2'b10));
    
    Rules m15 = rules
        rule stage2_mult (stg2_mult_cnt matches tagged Just {.x});
             if (x<=5)
               begin
                  stg2a_data.shift(mult1.result);
                  stg2b_data.shift(mult2.result);
               end
             else if (x == 7)
               begin
                  stg2a_data.pongshift(mult1.result);
                  stg2b_data.pongshift (mult2.result);
               end
        endrule
    endrules;

    function Action fn3 (bit b, Int#(32) a);
        let temp = row ? a : a >> 3;
        let stg3 = (b==0) ? stg3_data.shift (temp) : stg3_data.pongshift(temp);
        return stg3;
    endfunction :fn3
        
    Rules m16 = cr ("stage3_0", stg3_cnt, 0, 
                    fn3 (0,adder1.start (stg2a_data.read [0], 
                                         row ? 128 : 65536, True)));
    Rules m17 = cr ("stage3_1", stg3_cnt, 1, 
                    fn3 (0,adder1.start (stg2b_data.read [3], 0 , True)));
    Rules m18 = cr ("stage3_2", stg3_cnt, 2, 
                    fn3 (0,adder1.start (stg2b_data.read [1], 
                                         stg2a_data.read [5], False)));
    Rules m19 = cr ("stage3_3", stg3_cnt, 3, 
                    fn3 (0,adder1.start (stg2b_data.read [5], 
                                         stg2a_data.read [2], True)));
    Rules m20 = cr ("stage3_4", stg3_cnt, 4, 
                    fn3 (0,adder1.start (stg2b_data.read [6], 
                                         stg2a_data.read [1], True)));
    Rules m21 = cr ("stage3_5", stg3_cnt, 5, 
                    fn3 (0,adder1.start (stg2b_data.read [0], 
                                         stg2a_data.read [6], False)));
    Rules m22 = cr ("stage3_6", stg3_cnt, 6, 
                    fn3 (0,adder1.start (stg2a_data.read [3], 
                                         stg2b_data.read [4], True)));
    Rules m23 = cr ("stage3_7", stg3_cnt, 7, 
                    fn3 (1,adder1.start (stg2a_data.read [4], 
                                         stg2b_data.read [2], False)));
    


    Rules m24 = cr ("stage4_0", stg4_cnt, 0,
                    stg4_data.shift (adder2.start (stg3_data.read[0], 
                                                   stg3_data.read[1], False)));
    Rules m25 = cr ("stage4_1", stg4_cnt, 1,
                    stg4_data.shift (adder2.start (stg3_data.read[4], 
                                                   stg3_data.read[6], True)));
    Rules m26 = cr ("stage4_2", stg4_cnt, 2,
                    stg4_data.shift (adder2.start (stg3_data.read[2], 
                                                   0, True)));
    Rules m27 = cr ("stage4_3", stg4_cnt, 3,
                    stg4_data.shift (adder2.start (stg3_data.read[3], 
                                                   0, True)));
    Rules m28 = cr ("stage4_4", stg4_cnt, 4,
                    stg4_data.shift (adder2.start (stg3_data.read[4], 
                                                   stg3_data.read[6], False)));
    Rules m29 = cr ("stage4_5", stg4_cnt, 5,
                    stg4_data.shift (adder2.start (stg3_data.read[5], 
                                                   stg3_data.read[7], False)));
    Rules m30 = cr ("stage4_6", stg4_cnt, 6,
                    stg4_data.shift (adder2.start (stg3_data.read[5], 
                                                   stg3_data.read[7], True)));
    Rules m31 = cr ("stage4_7", stg4_cnt, 7,
                    stg4_data.pongshift (adder2.start (stg3_data.read[0], 
                                                    stg3_data.read[1], True)));

    
  
    Rules m32 = cr ("stage5_0", stg5_cnt, 0, 
                    stg5_data.shift (adder3.start (stg4_data.read [0], 
                                                   stg4_data.read [2], False )));
    Rules m33 = cr ("stage5_1", stg5_cnt, 1, 
                    stg5_data.shift (adder3.start (stg4_data.read [4], 
                                                   stg4_data.read [5], True )));
    Rules m34 = cr ("stage5_2", stg5_cnt, 2, 
                    stg5_data.shift (adder3.start (stg4_data.read [0], 
                                                   stg4_data.read [2], True )));
    Rules m35 = cr ("stage5_3", stg5_cnt, 3, 
                    stg5_data.shift (adder3.start (stg4_data.read [4], 
                                                   stg4_data.read [5], False)));
    Rules m36 = cr ("stage5_4", stg5_cnt, 4, 
                    stg5_data.shift (adder3.start (stg4_data.read [7], 
                                                   stg4_data.read [3], True )) );
    Rules m37 = cr ("stage5_5", stg5_cnt, 5, 
                    stg5_data.shift (stg4_data.read [1]) );
    Rules m38 = cr ("stage5_6", stg5_cnt, 6, 
                    stg5_data.shift (adder3.start (stg4_data.read [7], 
                                                   stg4_data.read [3], False )));
    Rules m39 = cr ("stage5_7", stg5_cnt, 7, 
                    stg5_data.pongshift (stg4_data.read [6]) );

 
             
    Rules m40 = cr ("stage6_0", stg6_cnt, 0,
                    stg6_data.shift (mult181.start (stg5_data.read[1])) );
    Rules m41 = cr ("stage6_1", stg6_cnt, 1,
                    stg6_data.shift (stg5_data.read[5]) );
    Rules m42 = cr ("stage6_2", stg6_cnt, 2,
                    stg6_data.shift (stg5_data.read[2]) );
    Rules m43 = cr ("stage6_3", stg6_cnt, 3,
                    stg6_data.shift (stg5_data.read[0]) );
    Rules m44 = cr ("stage6_4", stg6_cnt, 4,
                    stg6_data.shift (stg5_data.read[7]) );
    Rules m45 = cr ("stage6_5", stg6_cnt, 5,
                    stg6_data.shift (stg5_data.read[4]) );
    Rules m46 = cr ("stage6_6", stg6_cnt, 6,
                    stg6_data.shift (stg5_data.read[6]) );
    Rules m47 = cr ("stage6_7", stg6_cnt, 7,
                    stg6_data.pongshift (mult181.start (stg5_data.read[3])) );
   
    Rules m48 = rules
    
           rule stage7 (stg7_cnt matches tagged Just {.x});
              case (out_cnt) matches
                 tagged Nothing : out_cnt <= Just (0);
                 tagged Just {.y} : out_cnt <= Just (y+1);
              endcase
           endrule

    endrules;

    function Action laststage (Integer a, Integer b, Bool c);
      action
         Nat const_num = (row) ? 8 : 14;
         let d_out_temp = (adder4.start 
                          (stg6_data.read[a], stg6_data.read[b],c)) >> const_num;
         d_out <= truncate (d_out_temp);
      endaction
    endfunction     

    Rules m49 = cr ("stage7_0", stg7_cnt, 0, laststage (5 ,1 ,True));
    Rules m50 = cr ("stage7_1", stg7_cnt, 1, laststage (2 ,0 ,True));
    Rules m51 = cr ("stage7_2", stg7_cnt, 2, laststage (3 ,7 ,True));
    Rules m52 = cr ("stage7_3", stg7_cnt, 3, laststage (6 ,4 ,True));
    Rules m53 = cr ("stage7_4", stg7_cnt, 4, laststage (6 ,4 ,False));
    Rules m54 = cr ("stage7_5", stg7_cnt, 5, laststage (3 ,7 ,False));
    Rules m55 = cr ("stage7_6", stg7_cnt, 6, laststage (2 ,0 ,False));
    Rules m56 = cr ("stage7_7", stg7_cnt, 7, laststage (5 ,1 ,False));

    

    List#(Rules) my_list = Cons (m01, Cons (m02, Cons (m03, Cons (m04, 
                           Cons (m05, Cons (m06, Cons (m07, Cons (m08, 
                           Cons (m09, Cons (m10, Cons (m11, Cons (m12, 
                           Cons (m13, Cons (m14, Cons (m15, Cons (m16, 
                           Cons (m17, Cons (m18, Cons (m19, Cons (m20, 
                           Cons (m21, Cons (m22, Cons (m23, Cons (m24, 
                           Cons (m25, Cons (m26, Cons (m27, Cons (m28, 
                           Cons (m29, Cons (m30, Cons (m31, Cons (m32, 
                           Cons (m33, Cons (m34, Cons (m35, Cons (m36, 
                           Cons (m37, Cons (m38, Cons (m39, Cons (m40, 
                           Cons (m41, Cons (m42, Cons (m43, Cons (m44, 
                           Cons (m45, Cons (m46, Cons (m47, Cons (m48, 
                           Cons (m49, Cons (m50, Cons (m51, Cons (m52, 
                           Cons (m53, Cons (m54, Cons (m55, Cons (m56, 
                           nil)))))))))))))))))))))))))))))))))))))))))
                           )))))))))))))));

   
   addRules (joinRules (my_list)) ;

    method Action start (d_in, strb);
        if (strb == 1)
         begin
           stg1_cnt <= Just (0);
           stg1_data.shift (signExtend(d_in));
         end
        else if (stg1_cnt matches tagged Just {.x})
         begin
           if (x==63)
              stg1_cnt <= Nothing;
           else
              stg1_cnt <= Just (x+1);
           if (x[2:0]==6)
              stg1_data.pongshift (signExtend(d_in));
           else
              stg1_data.shift(signExtend(d_in));
         end        
    endmethod : start
    
    method result ();
        let valid = (out_cnt == Just (0)) ? 1:0;
        Int#(w_out) output_val;
             if (row)
               output_val = truncate (d_out);
             else if (d_out < -256)
               output_val = -256;
             else if (d_out > 255)
               output_val = 255;
             else
               output_val = truncate (d_out);
                                     
        return (tuple2 (output_val,valid)); 
    endmethod : result
    

endmodule : mkIDCT_1D


endpackage : MkIDCT_1D
