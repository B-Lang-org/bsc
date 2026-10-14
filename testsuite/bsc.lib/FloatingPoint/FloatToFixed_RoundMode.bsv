import FixedPoint::*;
import FloatingPoint::*;
import Vector::*;
import GetPut::*;
import ClientServer::*;
import StmtFSM::*;

(* synthesize *)
module sysFloatToFixed_RoundMode();

    // Use single-precision parameters
    Integer e_size = 8;
    Integer m_size = 23;
    Integer isize_val = 32; // 32 integer bits
    Integer fsize_val = 0;   // 0 fractional bits (just integer)
    Integer ln_val = 0;      // No fractional shift

    let nan = unpack(32'b01111111110000000000000000000000);

    let inf = unpack(32'b01111111100000000000000000000000);

    let neginf = unpack(32'b11111111100000000000000000000000);

    let zero = unpack(32'b00000000000000000000000000000000);

    let quarter = unpack(32'b00111110100000000000000000000000);

    let half = unpack(32'b00111111000000000000000000000000);

    let one = unpack(32'b00111111100000000000000000000000);

    let one_and_half = unpack(32'b00111111110000000000000000000000);

    let neg_denorm = unpack(32'b10000000000000000000000000000001);

    let pos_denorm = unpack(32'b00000000000000000000000000000001);

    let minus_one_and_half = unpack(32'b10111111110000000000000000000000);

    rule test;
        $display("=== Testing NaN ===");

        // Convert to integer
        FloatingPoint#(8,23) fp_val1 = nan;
        Tuple2#(FixedPoint#(32,0), FloatingPoint::Exception) result1 = vFloatToFixed(5'b0, fp_val1, Rnd_Nearest_Even);
        FixedPoint#(32,0) fx1 = tpl_1(result1);
        $display("%0x", fx1.i);

        $display("=== Testing Inf  ===");

        // Convert to integer
        FloatingPoint#(8,23) fp_val2 = inf;
        Tuple2#(FixedPoint#(32,0), FloatingPoint::Exception) result2 = vFloatToFixed(5'b0, fp_val2, Rnd_Nearest_Even);
        FixedPoint#(32,0) fx2 = tpl_1(result2);
        $display("%0x", fx2.i);

        $display("=== Testing -Inf  ===");

        // Convert to integer
        FloatingPoint#(8,23) fp_val3 = neginf;
        Tuple2#(FixedPoint#(32,0), FloatingPoint::Exception) result3 = vFloatToFixed(5'b0, fp_val3, Rnd_Nearest_Even);
        FixedPoint#(32,0) fx3 = tpl_1(result3);
        $display("%0x", fx3.i);

        $display("=== Testing Zero  ===");

        // Convert to integer
        FloatingPoint#(8,23) fp_val4 = zero;
        Tuple2#(FixedPoint#(32,0), FloatingPoint::Exception) result4 = vFloatToFixed(5'b0, fp_val4, Rnd_Nearest_Even);
        FixedPoint#(32,0) fx4 = tpl_1(result4);
        $display("%0x", fx4.i);

        $display("=== Testing Quarter  ===");

        // Convert to integer
        FloatingPoint#(8,23) fp_val5 = quarter;
        Tuple2#(FixedPoint#(32,0), FloatingPoint::Exception) result5 = vFloatToFixed(5'b0, fp_val5, Rnd_Nearest_Even);
        FixedPoint#(32,0) fx5 = tpl_1(result5);
        $display("%0x", fx5.i);

        $display("=== Testing Half ===");

        // Convert to integer
        FloatingPoint#(8,23) fp_val6 = half;
        Tuple2#(FixedPoint#(32,0), FloatingPoint::Exception) result6 = vFloatToFixed(5'b0, fp_val6, Rnd_Nearest_Even);
        FixedPoint#(32,0) fx6 = tpl_1(result6);
        $display("%0x", fx6.i);

        $display("=== Testing One ===");

        // Convert to integer
        FloatingPoint#(8,23) fp_val7 = one;
        Tuple2#(FixedPoint#(32,0), FloatingPoint::Exception) result7 = vFloatToFixed(5'b0, fp_val7, Rnd_Nearest_Even);
        FixedPoint#(32,0) fx7 = tpl_1(result7);
        $display("%0x", fx7.i);

        $display("=== Testing One and Half ===");

        // Convert to integer
        FloatingPoint#(8,23) fp_val8 = one_and_half;
        Tuple2#(FixedPoint#(32,0), FloatingPoint::Exception) result8 = vFloatToFixed(5'b0, fp_val8, Rnd_Nearest_Even);
        FixedPoint#(32,0) fx8 = tpl_1(result8);
        $display("%0x", fx8.i);

        $display("=== Testing One ===");

        // Convert to integer
        FloatingPoint#(8,23) fp_val9 = one;
        Tuple2#(FixedPoint#(32,0), FloatingPoint::Exception) result9 = vFloatToFixed(5'b0, fp_val9, Rnd_Minus_Inf);
        FixedPoint#(32,0) fx9 = tpl_1(result9);
        $display("%0x", fx9.i);

        $display("=== Testing One and Half ===");

        // Convert to integer
        FloatingPoint#(8,23) fp_val10 = one_and_half;
        Tuple2#(FixedPoint#(32,0), FloatingPoint::Exception) result10 = vFloatToFixed(5'b0, fp_val10, Rnd_Minus_Inf);
        FixedPoint#(32,0) fx10 = tpl_1(result10);
        $display("%0x", fx10.i);

        $display("=== Testing Negative Denormalized ===");

        // Convert to integer
        FloatingPoint#(8,23) fp_val11 = neg_denorm;
        Tuple2#(FixedPoint#(32,0), FloatingPoint::Exception) result11 = vFloatToFixed(5'b0, fp_val11, Rnd_Minus_Inf);
        FixedPoint#(32,0) fx11 = tpl_1(result11);
        $display("%0x", fx11.i);

        $display("=== Testing One ===");

        // Convert to integer
        FloatingPoint#(8,23) fp_val12 = one;
        Tuple2#(FixedPoint#(32,0), FloatingPoint::Exception) result12 = vFloatToFixed(5'b0, fp_val12, Rnd_Plus_Inf);
        FixedPoint#(32,0) fx12 = tpl_1(result12);
        $display("%0x", fx12.i);

        $display("=== Testing One and Half ===");

        // Convert to integer
        FloatingPoint#(8,23) fp_val13 = one_and_half;
        Tuple2#(FixedPoint#(32,0), FloatingPoint::Exception) result13 = vFloatToFixed(5'b0, fp_val13, Rnd_Plus_Inf);
        FixedPoint#(32,0) fx13 = tpl_1(result13);
        $display("%0x", fx13.i);

        $display("=== Testing Postive Denormalized ===");

        // Convert to integer
        FloatingPoint#(8,23) fp_val14 = pos_denorm;
        Tuple2#(FixedPoint#(32,0), FloatingPoint::Exception) result14 = vFloatToFixed(5'b0, fp_val14, Rnd_Plus_Inf);
        FixedPoint#(32,0) fx14 = tpl_1(result14);
        $display("%0x", fx14.i);

        $display("=== Testing One ===");

        // Convert to integer
        FloatingPoint#(8,23) fp_val15 = one;
        Tuple2#(FixedPoint#(32,0), FloatingPoint::Exception) result15 = vFloatToFixed(5'b0, fp_val15, Rnd_Zero);
        FixedPoint#(32,0) fx15 = tpl_1(result15);
        $display("%0x", fx15.i);

        $display("=== Testing One and Half ===");

        // Convert to integer
        FloatingPoint#(8,23) fp_val16 = one_and_half;
        Tuple2#(FixedPoint#(32,0), FloatingPoint::Exception) result16 = vFloatToFixed(5'b0, fp_val16, Rnd_Zero);
        FixedPoint#(32,0) fx16 = tpl_1(result16);
        $display("%0x", fx16.i);

        $display("=== Testing Minus One and Half ===");

        // Convert to integer
        FloatingPoint#(8,23) fp_val17 = minus_one_and_half;
        Tuple2#(FixedPoint#(32,0), FloatingPoint::Exception) result17 = vFloatToFixed(5'b0, fp_val17, Rnd_Zero);
        FixedPoint#(32,0) fx17 = tpl_1(result17);
        $display("%0x", fx17.i);

        $finish;
    endrule

endmodule
