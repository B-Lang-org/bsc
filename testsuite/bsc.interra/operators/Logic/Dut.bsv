package Dut;
import Vector::*;

interface DUT;
method Action start(Bit#(129) a,Bit#(129) b);
method Bit#(129) bOr;
method Bit#(128) bOr_127;
method Bit#(127) bOr_126;
method Bit#(97) bOr_96;
method Bit#(96) bOr_95;
method Bit#(95) bOr_94;
method Bit#(65) bOr_64;
method Bit#(64) bOr_63;
method Bit#(63) bOr_62;
method Bit#(33) bOr_32;
method Bit#(32) bOr_31;
method Bit#(31) bOr_30;
method Bit#(2) bOr_1;
method Bit#(1) bOr_0;

method Bit#(129) bAnd;
method Bit#(128) bAnd_127;
method Bit#(127) bAnd_126;
method Bit#(97) bAnd_96;
method Bit#(96) bAnd_95;
method Bit#(95) bAnd_94;
method Bit#(65) bAnd_64;
method Bit#(64) bAnd_63;
method Bit#(63) bAnd_62;
method Bit#(33) bAnd_32;
method Bit#(32) bAnd_31;
method Bit#(31) bAnd_30;
method Bit#(2) bAnd_1;
method Bit#(1) bAnd_0;

method Bit#(129) bInv;
method Bit#(128) bInv_127;
method Bit#(127) bInv_126;
method Bit#(97) bInv_96;
method Bit#(96) bInv_95;
method Bit#(95) bInv_94;
method Bit#(65) bInv_64;
method Bit#(64) bInv_63;
method Bit#(63) bInv_62;
method Bit#(33) bInv_32;
method Bit#(32) bInv_31;
method Bit#(31) bInv_30;
method Bit#(2) bInv_1;
method Bit#(1) bInv_0;

method Bit#(129) bXor;
method Bit#(128) bXor_127;
method Bit#(127) bXor_126;
method Bit#(97) bXor_96;
method Bit#(96) bXor_95;
method Bit#(95) bXor_94;
method Bit#(65) bXor_64;
method Bit#(64) bXor_63;
method Bit#(63) bXor_62;
method Bit#(33) bXor_32;
method Bit#(32) bXor_31;
method Bit#(31) bXor_30;
method Bit#(2) bXor_1;
method Bit#(1) bXor_0;

method Bit#(129) bXnor;
method Bit#(128) bXnor_127;
method Bit#(127) bXnor_126;
method Bit#(97) bXnor_96;
method Bit#(96) bXnor_95;
method Bit#(95) bXnor_94;
method Bit#(65) bXnor_64;
method Bit#(64) bXnor_63;
method Bit#(63) bXnor_62;
method Bit#(33) bXnor_32;
method Bit#(32) bXnor_31;
method Bit#(31) bXnor_30;
method Bit#(2) bXnor_1;
method Bit#(1) bXnor_0;
endinterface : DUT


(*synthesize, always_ready, always_enabled*)
module mkDut(DUT);

Reg#(Bit#(129)) a <- mkReg(0);
Reg#(Bit#(129)) b <- mkReg(0);

method Action start(Bit#(129) in1, Bit#(129) in2);
 a <= in1;
 b <= in2;
endmethod


method Bit#(129) bOr;
bOr = (a|b);
endmethod


method Bit#(128) bOr_127;
bOr_127 = (a[127:0]|b[127:0]);
endmethod


method Bit#(127) bOr_126;
bOr_126 = (a[126:0]|b[126:0]);
endmethod


method Bit#(97) bOr_96;
bOr_96 = (a[96:0]|b[96:0]);
endmethod


method Bit#(96) bOr_95;
bOr_95 = (a[95:0]|b[95:0]);
endmethod


method Bit#(95) bOr_94;
bOr_94 = (a[94:0]|b[94:0]);
endmethod


method Bit#(65) bOr_64;
bOr_64 = (a[64:0]|b[64:0]);
endmethod


method Bit#(64) bOr_63;
bOr_63 = (a[63:0]|b[63:0]);
endmethod


method Bit#(63) bOr_62;
bOr_62 = (a[62:0]|b[62:0]);
endmethod


method Bit#(33) bOr_32;
bOr_32 = (a[32:0]|b[32:0]);
endmethod


method Bit#(32) bOr_31;
bOr_31 = (a[31:0]|b[31:0]);
endmethod


method Bit#(31) bOr_30;
bOr_30 = (a[30:0]|b[30:0]);
endmethod


method Bit#(2) bOr_1;
bOr_1 = (a[1:0]|b[1:0]);
endmethod


method Bit#(1) bOr_0;
bOr_0 = (a[0]|b[0]);
endmethod


method Bit#(129) bAnd;
bAnd = (a&b);
endmethod


method Bit#(128) bAnd_127;
bAnd_127 = (a[127:0]&b[127:0]);
endmethod


method Bit#(127) bAnd_126;
bAnd_126 = (a[126:0]&b[126:0]);
endmethod


method Bit#(97) bAnd_96;
bAnd_96 = (a[96:0]&b[96:0]);
endmethod


method Bit#(96) bAnd_95;
bAnd_95 = (a[95:0]&b[95:0]);
endmethod


method Bit#(95) bAnd_94;
bAnd_94 = (a[94:0]&b[94:0]);
endmethod


method Bit#(65) bAnd_64;
bAnd_64 = (a[64:0]&b[64:0]);
endmethod


method Bit#(64) bAnd_63;
bAnd_63 = (a[63:0]&b[63:0]);
endmethod


method Bit#(63) bAnd_62;
bAnd_62 = (a[62:0]&b[62:0]);
endmethod


method Bit#(33) bAnd_32;
bAnd_32 = (a[32:0]&b[32:0]);
endmethod


method Bit#(32) bAnd_31;
bAnd_31 = (a[31:0]&b[31:0]);
endmethod


method Bit#(31) bAnd_30;
bAnd_30 = (a[30:0]&b[30:0]);
endmethod


method Bit#(2) bAnd_1;
bAnd_1 = (a[1:0]&b[1:0]);
endmethod


method Bit#(1) bAnd_0;
bAnd_0 = (a[0]&b[0]);
endmethod


method Bit#(129) bXor;
bXor = (a^b);
endmethod


method Bit#(128) bXor_127;
bXor_127 = (a[127:0]^b[127:0]);
endmethod


method Bit#(127) bXor_126;
bXor_126 = (a[126:0]^b[126:0]);
endmethod


method Bit#(97) bXor_96;
bXor_96 = (a[96:0]^b[96:0]);
endmethod


method Bit#(96) bXor_95;
bXor_95 = (a[95:0]^b[95:0]);
endmethod


method Bit#(95) bXor_94;
bXor_94 = (a[94:0]^b[94:0]);
endmethod


method Bit#(65) bXor_64;
bXor_64 = (a[64:0]^b[64:0]);
endmethod


method Bit#(64) bXor_63;
bXor_63 = (a[63:0]^b[63:0]);
endmethod


method Bit#(63) bXor_62;
bXor_62 = (a[62:0]^b[62:0]);
endmethod


method Bit#(33) bXor_32;
bXor_32 = (a[32:0]^b[32:0]);
endmethod


method Bit#(32) bXor_31;
bXor_31 = (a[31:0]^b[31:0]);
endmethod


method Bit#(31) bXor_30;
bXor_30 = (a[30:0]^b[30:0]);
endmethod


method Bit#(2) bXor_1;
bXor_1 = (a[1:0]^b[1:0]);
endmethod


method Bit#(1) bXor_0;
bXor_0 = (a[0]^b[0]);
endmethod


method Bit#(129) bXnor;
bXnor = (a~^b);
endmethod


method Bit#(128) bXnor_127;
bXnor_127 = (a[127:0]~^b[127:0]);
endmethod


method Bit#(127) bXnor_126;
bXnor_126 = (a[126:0]~^b[126:0]);
endmethod


method Bit#(97) bXnor_96;
bXnor_96 = (a[96:0]~^b[96:0]);
endmethod


method Bit#(96) bXnor_95;
bXnor_95 = (a[95:0]~^b[95:0]);
endmethod


method Bit#(95) bXnor_94;
bXnor_94 = (a[94:0]~^b[94:0]);
endmethod


method Bit#(65) bXnor_64;
bXnor_64 = (a[64:0]~^b[64:0]);
endmethod


method Bit#(64) bXnor_63;
bXnor_63 = (a[63:0]~^b[63:0]);
endmethod


method Bit#(63) bXnor_62;
bXnor_62 = (a[62:0]~^b[62:0]);
endmethod


method Bit#(33) bXnor_32;
bXnor_32 = (a[32:0]~^b[32:0]);
endmethod


method Bit#(32) bXnor_31;
bXnor_31 = (a[31:0]~^b[31:0]);
endmethod


method Bit#(31) bXnor_30;
bXnor_30 = (a[30:0]~^b[30:0]);
endmethod


method Bit#(2) bXnor_1;
bXnor_1 = (a[1:0]~^b[1:0]);
endmethod


method Bit#(1) bXnor_0;
bXnor_0 = (a[0]~^b[0]);
endmethod


method Bit#(129) bInv;
bInv = ~a;
endmethod


method Bit#(128) bInv_127;
bInv_127 = ~a[127:0];
endmethod


method Bit#(127) bInv_126;
bInv_126 = ~a[126:0];
endmethod


method Bit#(97) bInv_96;
bInv_96 = ~a[96:0];
endmethod


method Bit#(96) bInv_95;
bInv_95 = ~a[95:0];
endmethod


method Bit#(95) bInv_94;
bInv_94 = ~a[94:0];
endmethod


method Bit#(65) bInv_64;
bInv_64 = ~a[64:0];
endmethod


method Bit#(64) bInv_63;
bInv_63 = ~a[63:0];
endmethod


method Bit#(63) bInv_62;
bInv_62 = ~a[62:0];
endmethod


method Bit#(33) bInv_32;
bInv_32 = ~a[32:0];
endmethod


method Bit#(32) bInv_31;
bInv_31 = ~a[31:0];
endmethod


method Bit#(31) bInv_30;
bInv_30 = ~a[30:0];
endmethod


method Bit#(2) bInv_1;
bInv_1 = ~a[1:0];
endmethod


method Bit#(1) bInv_0;
bInv_0 = ~a[0];
endmethod



endmodule

endpackage
