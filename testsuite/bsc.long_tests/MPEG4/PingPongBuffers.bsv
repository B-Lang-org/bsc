//////////////////////////////////////////////////////////////////
/* Ping Pong Buffers.
   The method shift shifts d_in into a list of registers stg1a_data.
   The method pongshift transfers data in parallel from stg1a_data to stg1b_data
*/
package PingPongBuffers;

import ListN :: *;
import ListReg :: *;

interface Pingpong_IFC#(type a, type n) ;
    method Action shift (Int#(a) d_in);
    method Action pongshift (Int#(a) d_in);
    method ListN#(n, Int#(a)) read();
endinterface : Pingpong_IFC


module pingpong (Pingpong_IFC#(a,n)) provisos (Add#(depth, 1, n), 
                                               Add#(xyz, 1, depth));

   Reg#(ListN#(depth, Int#(a))) stg1a_data() ;
   mkReg#(replicate(0)) i_stg1a_data(stg1a_data) ;

   Reg#(ListN#(n,Int#(a))) stg1b_data() ;
   mkReg#(replicate(0)) i_stg1b_data(stg1b_data) ;

   method Action shift (d_in);
      // create a new list with d_in at its head and
      // all but the last elem of stg1a_data
      stg1a_data <= cons (d_in, init (stg1a_data));
   endmethod : shift

   method Action pongshift (d_in);
      // Shift stage1a into state1b
      stg1b_data <= cons (d_in, stg1a_data);
   endmethod : pongshift

   method read();
      // parallel read of stage 2 data
      return (reverse (stg1b_data));
   endmethod : read
endmodule

(* synthesize *)
module pingpong_12_7 (Pingpong_IFC#(12,8));
    Pingpong_IFC#(12,8) p();
    pingpong the_p (p);
    return (p);
endmodule : pingpong_12_7

(* synthesize *)
module pingpong_32_6 (Pingpong_IFC#(32,7));
    Pingpong_IFC#(32,7) p();
    pingpong the_p (p) ;
    return (p);
endmodule : pingpong_32_6

(* synthesize *)
module pingpong_32_7 (Pingpong_IFC#(32,8));
    Pingpong_IFC#(32,8) p();
    pingpong the_p (p);
    return (p);
endmodule : pingpong_32_7

(* synthesize *)
module pingpong_16_7 (Pingpong_IFC#(16,8));
    Pingpong_IFC#(16,8) p ();
    pingpong the_p(p);
    return (p);
endmodule : pingpong_16_7

endpackage : PingPongBuffers
