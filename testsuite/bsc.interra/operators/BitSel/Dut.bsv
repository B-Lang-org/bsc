package Dut;
import Vector::*;

interface DUT;
method Action start(Bit#(128) a);
method Bit#(6) ex_crs_1_1;
method Bit#(6) ex_crs_1_2;
method Bit#(6) ex_crs_1_3;
method Bit#(36) ex_crs_2_1;
method Bit#(36) ex_crs_2_2;
method Bit#(66) ex_crs_3;
method Bit#(6) ex_tch_1_1;
method Bit#(6) ex_tch_1_2;
method Bit#(6) ex_tch_1_3;
method Bit#(6) ex_tch_1_4;
method Bit#(6) ex_tch_1_5;
method Bit#(6) ex_tch_1_6;
method Bit#(32) ex_tch_2_1;
method Bit#(32) ex_tch_2_2;
method Bit#(32) ex_tch_2_3;
method Bit#(64) ex_tch_2_4;
method Bit#(64) ex_tch_2_5;
method Bit#(96) ex_tch_2_6;
method Bit#(36) con_crs_1;
method Bit#(68) con_crs_2;
method Bit#(100) con_crs_3;
method Bit#(32) con_tch_1_1;
method Bit#(64) con_tch_1_2;
method Bit#(96) con_tch_1_3;
method Bit#(128) con_tch_1_4;
endinterface : DUT


(*synthesize, always_ready, always_enabled*)
module mkDut(DUT);

Reg#(Bit#(128)) a <- mkReg(0);

method Action start(Bit#(128) in1);
 a <= in1;
endmethod


method Bit#(6) ex_crs_1_1;
ex_crs_1_1 = a[34:29];
endmethod


method Bit#(6) ex_crs_1_2;
ex_crs_1_2 = a[66:61];
endmethod


method Bit#(6) ex_crs_1_3;
ex_crs_1_3 = a[98:93];
endmethod


method Bit#(36) ex_crs_2_1;
ex_crs_2_1 = a[65:30];
endmethod


method Bit#(36) ex_crs_2_2;
ex_crs_2_2 = a[97:62];
endmethod


method Bit#(66) ex_crs_3;
ex_crs_3 = a[96:31];
endmethod


method Bit#(6) ex_tch_1_1;
ex_tch_1_1 = a[31:26];
endmethod


method Bit#(6) ex_tch_1_2;
ex_tch_1_2 = a[63:58];
endmethod


method Bit#(6) ex_tch_1_3;
ex_tch_1_3 = a[95:90];
endmethod


method Bit#(6) ex_tch_1_4;
ex_tch_1_4 = a[101:96];
endmethod


method Bit#(6) ex_tch_1_5;
ex_tch_1_5 = a[69:64];
endmethod


method Bit#(6) ex_tch_1_6;
ex_tch_1_6 = a[37:32];
endmethod


method Bit#(32) ex_tch_2_1;
ex_tch_2_1 = a[63:32];
endmethod


method Bit#(32) ex_tch_2_2;
ex_tch_2_2 = a[95:64];
endmethod


method Bit#(32) ex_tch_2_3;
ex_tch_2_3 = a[127:96];
endmethod


method Bit#(64) ex_tch_2_4;
ex_tch_2_4 = a[127:64];
endmethod


method Bit#(64) ex_tch_2_5;
ex_tch_2_5 = a[95:32];
endmethod


method Bit#(96) ex_tch_2_6;
ex_tch_2_6 = a[127:32];
endmethod


method Bit#(36) con_crs_1;
con_crs_1 = {a[31:26],a[63:58],a[95:90],a[101:96],a[69:64],a[37:32]};
endmethod


method Bit#(68) con_crs_2;
con_crs_2 = {a[63:32],a[95:64],4'd2};
endmethod


method Bit#(100) con_crs_3;
con_crs_3 = {a[31:26],a[63:58],a[95:90],a[101:96],a[69:64],a[37:32],a[127:64]};
endmethod


method Bit#(32) con_tch_1_1;
con_tch_1_1 = {a[31:26],a[63:58],a[95:90],a[101:96],a[69:64],2'd2};
endmethod


method Bit#(64) con_tch_1_2;
con_tch_1_2 = {a[63:32],a[95:64]};
endmethod


method Bit#(96) con_tch_1_3;
con_tch_1_3 = {a[63:32],a[95:64],a[127:96]};
endmethod


method Bit#(128) con_tch_1_4;
con_tch_1_4 = {a[63:32],a[63:32],a[95:64],a[127:96]};
endmethod


endmodule

endpackage
