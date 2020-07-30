interface DESIGN_IFC_SBOX1 #(parameter type a,parameter type b);
   method b dout(a addr);
endinterface: DESIGN_IFC_SBOX1

(* 
       synthesize,
       always_ready ,
       always_enabled ,
       CLK = "clk",
       RST_N = "reset"
 *)

module mkSbox1 (DESIGN_IFC_SBOX1 #(Bit#(6),Bit#(4)));

method Bit#(4) dout(Bit#(6) addr);

  
    case ({addr[5:5], addr[0:0], addr[4:1]}) 
         0:  dout =  14;
         1:  dout =   4;
         2:  dout =  13;
         3:  dout =   1;
         4:  dout =   2;
         5:  dout =  15;
         6:  dout =  11;
         7:  dout =   8;
         8:  dout =   3;
         9:  dout =  10;
        10:  dout =   6;
        11:  dout =  12;
        12:  dout =   5;
        13:  dout =   9;
        14:  dout =   0;
        15:  dout =   7;

        16:  dout =   0;
        17:  dout =  15;
        18:  dout =   7;
        19:  dout =   4;
        20:  dout =  14;
        21:  dout =   2;
        22:  dout =  13;
        23:  dout =   1;
        24:  dout =  10;
        25:  dout =   6;
        26:  dout =  12;
        27:  dout =  11;
        28:  dout =   9;
        29:  dout =   5;
        30:  dout =   3;
        31:  dout =   8;

        32:  dout =   4;
        33:  dout =   1;
        34:  dout =  14;
        35:  dout =   8;
        36:  dout =  13;
        37:  dout =   6;
        38:  dout =   2;
        39:  dout =  11;
        40:  dout =  15;
        41:  dout =  12;
        42:  dout =   9;
        43:  dout =   7;
        44:  dout =   3;
        45:  dout =  10;
        46:  dout =   5;
        47:  dout =   0;

        48:  dout =  15;
        49:  dout =  12;
        50:  dout =   8;
        51:  dout =   2;
        52:  dout =   4;
        53:  dout =   9;
        54:  dout =   1;
        55:  dout =   7;
        56:  dout =   5;
        57:  dout =  11;
        58:  dout =   3;
        59:  dout =  14;
        60:  dout =  10;
        61:  dout =   0;
        62:  dout =   6;
        63:  dout =  13;

    endcase
    endmethod: dout

endmodule: mkSbox1



interface DESIGN_IFC_SBOX2;
   method Bit#(4) dout(Bit#(6) addr);
endinterface: DESIGN_IFC_SBOX2

(*
       synthesize,
       always_ready ,
       always_enabled ,
       CLK = "clk",
       RST_N = "reset"
 *)

module mkSbox2 (DESIGN_IFC_SBOX2);

method Bit#(4) dout(Bit#(6) addr);

   case ({addr[5:5], addr[0:0], addr[4:1]})
         0:  dout = 15;
         1:  dout =  1;
         2:  dout =  8;
         3:  dout = 14;
         4:  dout =  6;
         5:  dout = 11;
         6:  dout =  3;
         7:  dout =  4;
         8:  dout =  9;
         9:  dout =  7;
        10:  dout =  2;
        11:  dout = 13;
        12:  dout = 12;
        13:  dout =  0;
        14:  dout =  5;
        15:  dout = 10;

        16:  dout =  3;
        17:  dout = 13;
        18:  dout =  4;
        19:  dout =  7;
        20:  dout = 15;
        21:  dout =  2;
        22:  dout =  8;
        23:  dout = 14;
        24:  dout = 12;
        25:  dout =  0;
        26:  dout =  1;
        27:  dout = 10;
        28:  dout =  6;
        29:  dout =  9;
        30:  dout = 11;
        31:  dout =  5;

        32:  dout =  0;
        33:  dout = 14;
        34:  dout =  7;
        35:  dout = 11;
        36:  dout = 10;
        37:  dout =  4;
        38:  dout = 13;
        39:  dout =  1;
        40:  dout =  5;
        41:  dout =  8;
        42:  dout = 12;
        43:  dout =  6;
        44:  dout =  9;
        45:  dout =  3;
        46:  dout =  2;
        47:  dout = 15;

        48:  dout = 13;
        49:  dout =  8;
        50:  dout = 10;
        51:  dout =  1;
        52:  dout =  3;
        53:  dout = 15;
        54:  dout =  4;
        55:  dout =  2;
        56:  dout = 11;
        57:  dout =  6;
        58:  dout =  7;
        59:  dout = 12;
        60:  dout =  0;
        61:  dout =  5;
        62:  dout = 14;
        63:  dout =  9;

    endcase
    endmethod: dout

endmodule: mkSbox2



interface DESIGN_IFC_SBOX3;
   method Bit#(4) dout(Bit#(6) addr);
endinterface: DESIGN_IFC_SBOX3

(*
       synthesize,
       always_ready ,
       always_enabled ,
       CLK = "clk",
       RST_N = "reset"
 *)

module mkSbox3 (DESIGN_IFC_SBOX3);

method Bit#(4) dout(Bit#(6) addr);
    case ({addr[5:5], addr[0:0], addr[4:1]})
         0:  dout = 10;
         1:  dout =  0;
         2:  dout =  9;
         3:  dout = 14;
         4:  dout =  6;
         5:  dout =  3;
         6:  dout = 15;
         7:  dout =  5;
         8:  dout =  1;
         9:  dout = 13;
        10:  dout = 12;
        11:  dout =  7;
        12:  dout = 11;
        13:  dout =  4;
        14:  dout =  2;
        15:  dout =  8;

        16:  dout = 13;
        17:  dout =  7;
        18:  dout =  0;
        19:  dout =  9;
        20:  dout =  3;
        21:  dout =  4;
        22:  dout =  6;
        23:  dout = 10;
        24:  dout =  2;
        25:  dout =  8;
        26:  dout =  5;
        27:  dout = 14;
        28:  dout = 12;
        29:  dout = 11;
        30:  dout = 15;
        31:  dout =  1;

        32:  dout = 13;
        33:  dout =  6;
        34:  dout =  4;
        35:  dout =  9;
        36:  dout =  8;
        37:  dout = 15;
        38:  dout =  3;
        39:  dout =  0;
        40:  dout = 11;
        41:  dout =  1;
        42:  dout =  2;
        43:  dout = 12;
        44:  dout =  5;
        45:  dout = 10;
        46:  dout = 14;
        47:  dout =  7;

        48:  dout =  1;
        49:  dout = 10;
        50:  dout = 13;
        51:  dout =  0;
        52:  dout =  6;
        53:  dout =  9;
        54:  dout =  8;
        55:  dout =  7;
        56:  dout =  4;
        57:  dout = 15;
        58:  dout = 14;
        59:  dout =  3;
        60:  dout = 11;
        61:  dout =  5;
        62:  dout =  2;
        63:  dout = 12;

    endcase
    endmethod: dout

endmodule: mkSbox3

interface DESIGN_IFC_SBOX4;
   method Bit#(4) dout(Bit#(6) addr);
endinterface: DESIGN_IFC_SBOX4

(*
       synthesize,  
       always_ready ,
       always_enabled ,
       CLK = "clk",
       RST_N = "reset"
 *)

module mkSbox4 (DESIGN_IFC_SBOX4);

method Bit#(4) dout(Bit#(6) addr);
    case ({addr[5:5], addr[0:0], addr[4:1]})

         0:  dout =  7;
         1:  dout = 13;
         2:  dout = 14;
         3:  dout =  3;
         4:  dout =  0;
         5:  dout =  6;
         6:  dout =  9;
         7:  dout = 10;
         8:  dout =  1;
         9:  dout =  2;
        10:  dout =  8;
        11:  dout =  5;
        12:  dout = 11;
        13:  dout = 12;
        14:  dout =  4;
        15:  dout = 15;

        16:  dout = 13;
        17:  dout =  8;
        18:  dout = 11;
        19:  dout =  5;
        20:  dout =  6;
        21:  dout = 15;
        22:  dout =  0;
        23:  dout =  3;
        24:  dout =  4;
        25:  dout =  7;
        26:  dout =  2;
        27:  dout = 12;
        28:  dout =  1;
        29:  dout = 10;
        30:  dout = 14;
        31:  dout =  9;

        32:  dout = 10;
        33:  dout =  6;
        34:  dout =  9;
        35:  dout =  0;
        36:  dout = 12;
        37:  dout = 11;
        38:  dout =  7;
        39:  dout = 13;
        40:  dout = 15;
        41:  dout =  1;
        42:  dout =  3;
        43:  dout = 14;
        44:  dout =  5;
        45:  dout =  2;
        46:  dout =  8;
        47:  dout =  4;

        48:  dout =  3;
        49:  dout = 15;
        50:  dout =  0;
        51:  dout =  6;
        52:  dout = 10;
        53:  dout =  1;
        54:  dout = 13;
        55:  dout =  8;
        56:  dout =  9;
        57:  dout =  4;
        58:  dout =  5;
        59:  dout = 11;
        60:  dout = 12;
        61:  dout =  7;
        62:  dout =  2;
        63:  dout = 14;

    endcase
    endmethod: dout

endmodule: mkSbox4

interface DESIGN_IFC_SBOX5;
   method Bit#(4) dout(Bit#(6) addr);
endinterface: DESIGN_IFC_SBOX5

(* 
       synthesize,
       always_ready ,
       always_enabled ,
       CLK = "clk",
       RST_N = "reset"
 *)

module mkSbox5 (DESIGN_IFC_SBOX5);

method Bit#(4) dout(Bit#(6) addr);
    case ({addr[5:5], addr[0:0], addr[4:1]})


         0:  dout =  2;
         1:  dout = 12;
         2:  dout =  4;
         3:  dout =  1;
         4:  dout =  7;
         5:  dout = 10;
         6:  dout = 11;
         7:  dout =  6;
         8:  dout =  8;
         9:  dout =  5;
        10:  dout =  3;
        11:  dout = 15;
        12:  dout = 13;
        13:  dout =  0;
        14:  dout = 14;
        15:  dout =  9;

        16:  dout = 14;
        17:  dout = 11;
        18:  dout =  2;
        19:  dout = 12;
        20:  dout =  4;
        21:  dout =  7;
        22:  dout = 13;
        23:  dout =  1;
        24:  dout =  5;
        25:  dout =  0;
        26:  dout = 15;
        27:  dout = 10;
        28:  dout =  3;
        29:  dout =  9;
        30:  dout =  8;
        31:  dout =  6;

        32:  dout =  4;
        33:  dout =  2;
        34:  dout =  1;
        35:  dout = 11;
        36:  dout = 10;
        37:  dout = 13;
        38:  dout =  7;
        39:  dout =  8;
        40:  dout = 15;
        41:  dout =  9;
        42:  dout = 12;
        43:  dout =  5;
        44:  dout =  6;
        45:  dout =  3;
        46:  dout =  0;
        47:  dout = 14;

        48:  dout = 11;
        49:  dout =  8;
        50:  dout = 12;
        51:  dout =  7;
        52:  dout =  1;
        53:  dout = 14;
        54:  dout =  2;
        55:  dout = 13;
        56:  dout =  6;
        57:  dout = 15;
        58:  dout =  0;
        59:  dout =  9;
        60:  dout = 10;
        61:  dout =  4;
        62:  dout =  5;
        63:  dout =  3;

    endcase
    endmethod: dout

endmodule: mkSbox5


interface DESIGN_IFC_SBOX6;
   method Bit#(4) dout(Bit#(6) addr);
endinterface: DESIGN_IFC_SBOX6

(* 
       synthesize,
       always_ready ,
       always_enabled ,
       CLK = "clk",
       RST_N = "reset"
 *)

module mkSbox6 (DESIGN_IFC_SBOX6);

method Bit#(4) dout(Bit#(6) addr);
    case ({addr[5:5], addr[0:0], addr[4:1]})

         0:  dout = 12;
         1:  dout =  1;
         2:  dout = 10;
         3:  dout = 15;
         4:  dout =  9;
         5:  dout =  2;
         6:  dout =  6;
         7:  dout =  8;
         8:  dout =  0;
         9:  dout = 13;
        10:  dout =  3;
        11:  dout =  4;
        12:  dout = 14;
        13:  dout =  7;
        14:  dout =  5;
        15:  dout = 11;

        16:  dout = 10;
        17:  dout = 15;
        18:  dout =  4;
        19:  dout =  2;
        20:  dout =  7;
        21:  dout = 12;
        22:  dout =  9;
        23:  dout =  5;
        24:  dout =  6;
        25:  dout =  1;
        26:  dout = 13;
        27:  dout = 14;
        28:  dout =  0;
        29:  dout = 11;
        30:  dout =  3;
        31:  dout =  8;

        32:  dout =  9;
        33:  dout = 14;
        34:  dout = 15;
        35:  dout =  5;
        36:  dout =  2;
        37:  dout =  8;
        38:  dout = 12;
        39:  dout =  3;
        40:  dout =  7;
        41:  dout =  0;
        42:  dout =  4;
        43:  dout = 10;
        44:  dout =  1;
        45:  dout = 13;
        46:  dout = 11;
        47:  dout =  6;

        48:  dout =  4;
        49:  dout =  3;
        50:  dout =  2;
        51:  dout = 12;
        52:  dout =  9;
        53:  dout =  5;
        54:  dout = 15;
        55:  dout = 10;
        56:  dout = 11;
        57:  dout = 14;
        58:  dout =  1;
        59:  dout =  7;
        60:  dout =  6;
        61:  dout =  0;
        62:  dout =  8;
        63:  dout = 13;

    endcase
    endmethod: dout

endmodule: mkSbox6


interface DESIGN_IFC_SBOX7;
   method Bit#(4) dout(Bit#(6) addr);
endinterface: DESIGN_IFC_SBOX7

(*
       synthesize, 
       always_ready ,
       always_enabled ,
       CLK = "clk",
       RST_N = "reset"
 *)

module mkSbox7 (DESIGN_IFC_SBOX7);

method Bit#(4) dout(Bit#(6) addr);
    case ({addr[5:5], addr[0:0], addr[4:1]})

         0:  dout =  4;
         1:  dout = 11;
         2:  dout =  2;
         3:  dout = 14;
         4:  dout = 15;
         5:  dout =  0;
         6:  dout =  8;
         7:  dout = 13;
         8:  dout =  3;
         9:  dout = 12;
        10:  dout =  9;
        11:  dout =  7;
        12:  dout =  5;
        13:  dout = 10;
        14:  dout =  6;
        15:  dout =  1;

        16:  dout = 13;
        17:  dout =  0;
        18:  dout = 11;
        19:  dout =  7;
        20:  dout =  4;
        21:  dout =  9;
        22:  dout =  1;
        23:  dout = 10;
        24:  dout = 14;
        25:  dout =  3;
        26:  dout =  5;
        27:  dout = 12;
        28:  dout =  2;
        29:  dout = 15;
        30:  dout =  8;
        31:  dout =  6;

        32:  dout =  1;
        33:  dout =  4;
        34:  dout = 11;
        35:  dout = 13;
        36:  dout = 12;
        37:  dout =  3;
        38:  dout =  7;
        39:  dout = 14;
        40:  dout = 10;
        41:  dout = 15;
        42:  dout =  6;
        43:  dout =  8;
        44:  dout =  0;
        45:  dout =  5;
        46:  dout =  9;
        47:  dout =  2;

        48:  dout =  6;
        49:  dout = 11;
        50:  dout = 13;
        51:  dout =  8;
        52:  dout =  1;
        53:  dout =  4;
        54:  dout = 10;
        55:  dout =  7;
        56:  dout =  9;
        57:  dout =  5;
        58:  dout =  0;
        59:  dout = 15;
        60:  dout = 14;
        61:  dout =  2;
        62:  dout =  3;
        63:  dout = 12;

    endcase
    endmethod: dout

endmodule: mkSbox7


interface DESIGN_IFC_SBOX8;
   method Bit#(4) dout(Bit#(6) addr);
endinterface: DESIGN_IFC_SBOX8

(*
       synthesize, 
       always_ready ,
       always_enabled ,
       CLK = "clk",
       RST_N = "reset"
 *)

module mkSbox8 (DESIGN_IFC_SBOX8);

method Bit#(4) dout(Bit#(6) addr);
    case ({addr[5:5], addr[0:0], addr[4:1]})
         0:  dout = 13;
         1:  dout =  2;
         2:  dout =  8;
         3:  dout =  4;
         4:  dout =  6;
         5:  dout = 15;
         6:  dout = 11;
         7:  dout =  1;
         8:  dout = 10;
         9:  dout =  9;
        10:  dout =  3;
        11:  dout = 14;
        12:  dout =  5;
        13:  dout =  0;
        14:  dout = 12;
        15:  dout =  7;

        16:  dout =  1;
        17:  dout = 15;
        18:  dout = 13;
        19:  dout =  8;
        20:  dout = 10;
        21:  dout =  3;
        22:  dout =  7;
        23:  dout =  4;
        24:  dout = 12;
        25:  dout =  5;
        26:  dout =  6;
        27:  dout = 11;
        28:  dout =  0;
        29:  dout = 14;
        30:  dout =  9;
        31:  dout =  2;

        32:  dout =  7;
        33:  dout = 11;
        34:  dout =  4;
        35:  dout =  1;
        36:  dout =  9;
        37:  dout = 12;
        38:  dout = 14;
        39:  dout =  2;
        40:  dout =  0;
        41:  dout =  6;
        42:  dout = 10;
        43:  dout = 13;
        44:  dout = 15;
        45:  dout =  3;
        46:  dout =  5;
        47:  dout =  8;

        48:  dout =  2;
        49:  dout =  1;
        50:  dout = 14;
        51:  dout =  7;
        52:  dout =  4;
        53:  dout = 10;
        54:  dout =  8;
        55:  dout = 13;
        56:  dout = 15;
        57:  dout = 12;
        58:  dout =  9;
        59:  dout =  0;
        60:  dout =  3;
        61:  dout =  5;
        62:  dout =  6;
        63:  dout = 11;

    endcase
    endmethod: dout

endmodule: mkSbox8


interface DESIGN_IFC_CRP;
   method Bit#(32) p(Bit#(32) r,Bit#(48) k_sub);
endinterface: DESIGN_IFC_CRP

(* 
       synthesize,
       always_ready ,
       always_enabled ,
       CLK = "clk",
       RST_N = "reset"
 *)

module mkCrp (DESIGN_IFC_CRP);

DESIGN_IFC_SBOX1 #(Bit#(6),Bit#(4)) inst_sbox1();
mkSbox1 the_inst_sbox1(inst_sbox1);

DESIGN_IFC_SBOX2 inst_sbox2();
mkSbox2 the_sbox2(inst_sbox2);

DESIGN_IFC_SBOX3 inst_sbox3();
mkSbox3 the_inst_sbox3(inst_sbox3);

DESIGN_IFC_SBOX4 inst_sbox4();
mkSbox4 the_inst_sbox4(inst_sbox4);

DESIGN_IFC_SBOX5 inst_sbox5();
mkSbox5 the_inst_sbox5(inst_sbox5);

DESIGN_IFC_SBOX6 inst_sbox6();
mkSbox6 the_inst_sbox6(inst_sbox6);

DESIGN_IFC_SBOX7 inst_sbox7();
mkSbox7 the_inst_sbox7(inst_sbox7);

DESIGN_IFC_SBOX8 inst_sbox8();
mkSbox8 the_inst_sbox8(inst_sbox8);


method Bit#(32) p(Bit#(32) r,Bit#(48) k_sub);
Bit#(48) e,x;
Bit#(32) s;
Bit#(4) sb1;
Bit#(4) sb2;
Bit#(4) sb3;
Bit#(4) sb4;
Bit#(4) sb5;
Bit#(4) sb6;
Bit#(4) sb7;
Bit#(4) sb8;

 e = {	r[0:0], r[31:31], r[30:30], r[29:29], r[28:28], r[27:27], r[28:28], r[27:27],
			r[26:26], r[25:25], r[24:24], r[23:23], r[24:24], r[23:23], r[22:22], r[21:21],
			r[20:20], r[19:19], r[20:20], r[19:19], r[18:18], r[17:17], r[16:16],
			r[15:15], r[16:16], r[15:15], r[14:14], r[13:13], r[12:12], r[11:11],
			r[12:12], r[11:11], r[10:10], r[9:9], r[8:8], r[7:7], r[8:8],
			r[7:7], r[6:6], r[5:5], r[4:4], r[3:3], r[4:4], r[3:3],
			r[2:2], r[1:1], r[0:0], r[31:31]};
 x = e ^ k_sub;

sb1 = inst_sbox1.dout(x[47:42]);
sb2 =  inst_sbox2.dout(x[41:36]);
sb3 = inst_sbox3.dout(x[35:30]);
sb4 = inst_sbox4.dout(x[29:24]);
sb5 = inst_sbox5.dout(x[23:18]);
sb6 = inst_sbox6.dout(x[17:12]);
sb7 = inst_sbox7.dout(x[11:6]);
sb8 = inst_sbox8.dout(x[5:0]);

s = {sb1,sb2,sb3,sb4,sb5,sb6,sb7,sb8};
//s  = {inst_sbox1.dout(x[47:42]),  inst_sbox2.dout(x[41:36]), inst_sbox3.dout(x[35:30]), inst_sbox4.dout(x[29:24]), inst_sbox5.dout(x[23:18]), inst_sbox6.dout(x[17:12]),inst_sbox7.dout(x[11:6]),inst_sbox8.dout(x[5:0])};



 p = {s[16:16], s[25:25], s[12:12], s[11:11], s[3:3], s[20:20], s[4:4],
      s[15:15], s[31:31], s[17:17], s[9:9], s[6:6], s[27:27], s[14:14],
      s[1:1], s[22:22], s[30:30], s[24:24], s[8:8], s[18:18], s[0:0],
      s[5:5], s[29:29], s[23:23], s[13:13], s[19:19], s[2:2], s[26:26],
      s[10:10], s[21:21], s[28:28], s[7:7]};

endmethod: p
endmodule: mkCrp


interface DESIGN_IFC_KEY_SEL;
    method Action getinputs(Bit#(56) k);
    method Bit#(48) k1(Bit#(1)  decrypt,Bit#(56) k);
    method Bit#(48) k2(Bit#(1)  decrpyt);
    method Bit#(48) k3(Bit#(1)  decrpyt);
    method Bit#(48) k4(Bit#(1)  decrpyt);
    method Bit#(48) k5(Bit#(1)  decrpyt);
    method Bit#(48) k6(Bit#(1)  decrpyt);
    method Bit#(48) k7(Bit#(1)  decrpyt);
    method Bit#(48) k8(Bit#(1)  decrpyt);
    method Bit#(48) k9(Bit#(1)  decrpyt);
    method Bit#(48) k10(Bit#(1) decrpyt);
    method Bit#(48) k11(Bit#(1) decrpyt);
    method Bit#(48) k12(Bit#(1) decrpyt);
    method Bit#(48) k13(Bit#(1) decrpyt);
    method Bit#(48) k14(Bit#(1) decrpyt);
    method Bit#(48) k15(Bit#(1) decrpyt);
    method Bit#(48) k16(Bit#(1) decrpyt);    
endinterface: DESIGN_IFC_KEY_SEL

(* 
       synthesize,
       always_ready ,
       always_enabled ,
       CLK = "clk",
       RST_N = "reset"
 *)

module mkKey_sel(DESIGN_IFC_KEY_SEL);


Reg #(Bit#(56)) k_r0   <- mkRegU;
Reg #(Bit#(56)) k_r1   <- mkRegU;
Reg #(Bit#(56)) k_r2   <- mkRegU;
Reg #(Bit#(56)) k_r3   <- mkRegU;
Reg #(Bit#(56)) k_r4   <- mkRegU;
Reg #(Bit#(56)) k_r5   <- mkRegU;
Reg #(Bit#(56)) k_r6   <- mkRegU;
Reg #(Bit#(56)) k_r7   <- mkRegU;
Reg #(Bit#(56)) k_r8   <- mkRegU;
Reg #(Bit#(56)) k_r9   <- mkRegU;
Reg #(Bit#(56)) k_r10  <- mkRegU;
Reg #(Bit#(56)) k_r11  <- mkRegU;
Reg #(Bit#(56)) k_r12  <- mkRegU;
Reg #(Bit#(56)) k_r13  <- mkRegU;
Reg #(Bit#(56)) k_r14  <- mkRegU;

method Action getinputs(Bit#(56) k);
 action
	k_r0  <=   k;
	k_r1  <=   k_r0;
	k_r2  <=   k_r1;
	k_r3  <=   k_r2;
	k_r4  <=   k_r3;
	k_r5  <=   k_r4;
	k_r6  <=   k_r5;
	k_r7  <=   k_r6;
	k_r8  <=   k_r7;
	k_r9  <=   k_r8;
	k_r10 <=   k_r9;
	k_r11 <=   k_r10;
	k_r12 <=   k_r11;
	k_r13 <=   k_r12;
	k_r14 <=   k_r13;
 endaction
endmethod: getinputs
 

method Bit#(48) k16(decrypt);
Bit#(48) result;
  result[47] = (decrypt == 1'b1) ? k_r14[47:47] : k_r14[40:40];
  result[46] = (decrypt == 1'b1) ? k_r14[11:11] : k_r14[4:4];
  result[45] = (decrypt == 1'b1) ? k_r14[26:26] : k_r14[19:19];
  result[44] = (decrypt == 1'b1) ? k_r14[3:3] : k_r14[53:53];
  result[43] = (decrypt == 1'b1) ? k_r14[13:13] : k_r14[6:6];
  result[42] = (decrypt == 1'b1) ? k_r14[41:41] : k_r14[34:34];
  result[41] = (decrypt == 1'b1) ? k_r14[27:27] : k_r14[20:20];
  result[40] = (decrypt == 1'b1) ? k_r14[6:6] : k_r14[24:24];
  result[39] = (decrypt == 1'b1) ? k_r14[54:54] : k_r14[47:47];
  result[38] = (decrypt == 1'b1) ? k_r14[48:48] : k_r14[41:41];
  result[37] = (decrypt == 1'b1) ? k_r14[39:39] : k_r14[32:32];
  result[36] = (decrypt == 1'b1) ? k_r14[19:19] : k_r14[12:12];
  result[35] = (decrypt == 1'b1) ? k_r14[53:53] : k_r14[46:46];
  result[34] = (decrypt == 1'b1) ? k_r14[25:25] : k_r14[18:18];
  result[33] = (decrypt == 1'b1) ? k_r14[33:33] : k_r14[26:26];
  result[32] = (decrypt == 1'b1) ? k_r14[34:34] : k_r14[27:27];
  result[31] = (decrypt == 1'b1) ? k_r14[17:17] : k_r14[10:10];
  result[30] = (decrypt == 1'b1) ? k_r14[5:5] : k_r14[55:55];
  result[29] = (decrypt == 1'b1) ? k_r14[4:4] : k_r14[54:54];
  result[28] = (decrypt == 1'b1) ? k_r14[55:55] : k_r14[48:48];
  result[27] = (decrypt == 1'b1) ? k_r14[24:24] : k_r14[17:17];
  result[26] = (decrypt == 1'b1) ? k_r14[32:32] : k_r14[25:25];
  result[25] = (decrypt == 1'b1) ? k_r14[40:40] : k_r14[33:33];
  result[24] = (decrypt == 1'b1) ? k_r14[20:20] : k_r14[13:13];
  result[23] = (decrypt == 1'b1) ? k_r14[36:36] : k_r14[29:29];
  result[22] = (decrypt == 1'b1) ? k_r14[31:31] : k_r14[51:51];
  result[21] = (decrypt == 1'b1) ? k_r14[21:21] : k_r14[14:14];
  result[20] = (decrypt == 1'b1) ? k_r14[8:8] : k_r14[1:1];
  result[19] = (decrypt == 1'b1) ? k_r14[23:23] : k_r14[16:16];
  result[18] = (decrypt == 1'b1) ? k_r14[52:52] : k_r14[45:45];
  result[17] = (decrypt == 1'b1) ? k_r14[14:14] : k_r14[7:7];
  result[16] = (decrypt == 1'b1) ? k_r14[29:29] : k_r14[22:22];
  result[15] = (decrypt == 1'b1) ? k_r14[51:51] : k_r14[44:44];
  result[14] = (decrypt == 1'b1) ? k_r14[9:9] : k_r14[2:2];
  result[13] = (decrypt == 1'b1) ? k_r14[35:35] : k_r14[28:28];
  result[12] = (decrypt == 1'b1) ? k_r14[30:30] : k_r14[23:23];
  result[11] = (decrypt == 1'b1) ? k_r14[2:2] : k_r14[50:50];
  result[10] = (decrypt == 1'b1) ? k_r14[37:37] : k_r14[30:30];
  result[9] = (decrypt == 1'b1) ? k_r14[22:22] : k_r14[15:15];
  result[8] = (decrypt == 1'b1) ? k_r14[0:0] : k_r14[52:52];
  result[7] = (decrypt == 1'b1) ? k_r14[42:42] : k_r14[35:35];
  result[6] = (decrypt == 1'b1) ? k_r14[38:38] : k_r14[31:31];
  result[5] = (decrypt == 1'b1) ? k_r14[16:16] : k_r14[9:9];
  result[4] = (decrypt == 1'b1) ? k_r14[43:43] : k_r14[36:36];
  result[3] = (decrypt == 1'b1) ? k_r14[44:44] : k_r14[37:37];
  result[2] = (decrypt == 1'b1) ? k_r14[1:1] : k_r14[49:49];
  result[1] = (decrypt == 1'b1) ? k_r14[7:7] : k_r14[0:0];
  result[0] = (decrypt == 1'b1) ? k_r14[28:28] : k_r14[21:21];
  k16 = result;
endmethod: k16

method Bit#(48) k15(decrypt);
  Bit#(48) result;
  result[47] = (decrypt == 1'b1) ? k_r13[54:54] : k_r13[33:33];
  result[46] = (decrypt == 1'b1) ? k_r13[18:18] : k_r13[54:54];
  result[45] = (decrypt == 1'b1) ? k_r13[33:33] : k_r13[12:12];
  result[44] = (decrypt == 1'b1) ? k_r13[10:10] : k_r13[46:46];
  result[43] = (decrypt == 1'b1) ? k_r13[20:20] : k_r13[24:24];
  result[42] = (decrypt == 1'b1) ? k_r13[48:48] : k_r13[27:27];
  result[41] = (decrypt == 1'b1) ? k_r13[34:34] : k_r13[13:13];
  result[40] = (decrypt == 1'b1) ? k_r13[13:13] : k_r13[17:17];
  result[39] = (decrypt == 1'b1) ? k_r13[4:4] : k_r13[40:40];
  result[38] = (decrypt == 1'b1) ? k_r13[55:55] : k_r13[34:34];
  result[37] = (decrypt == 1'b1) ? k_r13[46:46] : k_r13[25:25];
  result[36] = (decrypt == 1'b1) ? k_r13[26:26] : k_r13[5:5];
  result[35] = (decrypt == 1'b1) ? k_r13[3:3] : k_r13[39:39];
  result[34] = (decrypt == 1'b1) ? k_r13[32:32] : k_r13[11:11];
  result[33] = (decrypt == 1'b1) ? k_r13[40:40] : k_r13[19:19];
  result[32] = (decrypt == 1'b1) ? k_r13[41:41] : k_r13[20:20];
  result[31] = (decrypt == 1'b1) ? k_r13[24:24] : k_r13[3:3];
  result[30] = (decrypt == 1'b1) ? k_r13[12:12] : k_r13[48:48];
  result[29] = (decrypt == 1'b1) ? k_r13[11:11] : k_r13[47:47];
  result[28] = (decrypt == 1'b1) ? k_r13[5:5] : k_r13[41:41];
  result[27] = (decrypt == 1'b1) ? k_r13[6:6] : k_r13[10:10];
  result[26] = (decrypt == 1'b1) ? k_r13[39:39] : k_r13[18:18];
  result[25] = (decrypt == 1'b1) ? k_r13[47:47] : k_r13[26:26];
  result[24] = (decrypt == 1'b1) ? k_r13[27:27] : k_r13[6:6];
  result[23] = (decrypt == 1'b1) ? k_r13[43:43] : k_r13[22:22];
  result[22] = (decrypt == 1'b1) ? k_r13[38:38] : k_r13[44:44];
  result[21] = (decrypt == 1'b1) ? k_r13[28:28] : k_r13[7:7];
  result[20] = (decrypt == 1'b1) ? k_r13[15:15] : k_r13[49:49];
  result[19] = (decrypt == 1'b1) ? k_r13[30:30] : k_r13[9:9];
  result[18] = (decrypt == 1'b1) ? k_r13[0:0] : k_r13[38:38];
  result[17] = (decrypt == 1'b1) ? k_r13[21:21] : k_r13[0:0];
  result[16] = (decrypt == 1'b1) ? k_r13[36:36] : k_r13[15:15];
  result[15] = (decrypt == 1'b1) ? k_r13[31:31] : k_r13[37:37];
  result[14] = (decrypt == 1'b1) ? k_r13[16:16] : k_r13[50:50];
  result[13] = (decrypt == 1'b1) ? k_r13[42:42] : k_r13[21:21];
  result[12] = (decrypt == 1'b1) ? k_r13[37:37] : k_r13[16:16];
  result[11] = (decrypt == 1'b1) ? k_r13[9:9] : k_r13[43:43];
  result[10] = (decrypt == 1'b1) ? k_r13[44:44] : k_r13[23:23];
  result[9] = (decrypt == 1'b1) ? k_r13[29:29] : k_r13[8:8];
  result[8] = (decrypt == 1'b1) ? k_r13[7:7] : k_r13[45:45];
  result[7] = (decrypt == 1'b1) ? k_r13[49:49] : k_r13[28:28];
  result[6] = (decrypt == 1'b1) ? k_r13[45:45] : k_r13[51:51];
  result[5] = (decrypt == 1'b1) ? k_r13[23:23] : k_r13[2:2];
  result[4] = (decrypt == 1'b1) ? k_r13[50:50] : k_r13[29:29];
  result[3] = (decrypt == 1'b1) ? k_r13[51:51] : k_r13[30:30];
  result[2] = (decrypt == 1'b1) ? k_r13[8:8] : k_r13[42:42];
  result[1] = (decrypt == 1'b1) ? k_r13[14:14] : k_r13[52:52];
  result[0] = (decrypt == 1'b1) ? k_r13[35:35] : k_r13[14:14];
  k15 = result;
endmethod: k15

method Bit#(48) k14(decrypt );
  Bit#(48) result;
  result[47] = (decrypt == 1'b1) ? k_r12[11:11] : k_r12[19:19];
  result[46] = (decrypt == 1'b1) ? k_r12[32:32] : k_r12[40:40];
  result[45] = (decrypt == 1'b1) ? k_r12[47:47] : k_r12[55:55];
  result[44] = (decrypt == 1'b1) ? k_r12[24:24] : k_r12[32:32];
  result[43] = (decrypt == 1'b1) ? k_r12[34:34] : k_r12[10:10];
  result[42] = (decrypt == 1'b1) ? k_r12[5:5] : k_r12[13:13];
  result[41] = (decrypt == 1'b1) ? k_r12[48:48] : k_r12[24:24];
  result[40] = (decrypt == 1'b1) ? k_r12[27:27] : k_r12[3:3];
  result[39] = (decrypt == 1'b1) ? k_r12[18:18] : k_r12[26:26];
  result[38] = (decrypt == 1'b1) ? k_r12[12:12] : k_r12[20:20];
  result[37] = (decrypt == 1'b1) ? k_r12[3:3] : k_r12[11:11];
  result[36] = (decrypt == 1'b1) ? k_r12[40:40] : k_r12[48:48];
  result[35] = (decrypt == 1'b1) ? k_r12[17:17] : k_r12[25:25];
  result[34] = (decrypt == 1'b1) ? k_r12[46:46] : k_r12[54:54];
  result[33] = (decrypt == 1'b1) ? k_r12[54:54] : k_r12[5:5];
  result[32] = (decrypt == 1'b1) ? k_r12[55:55] : k_r12[6:6];
  result[31] = (decrypt == 1'b1) ? k_r12[13:13] : k_r12[46:46];
  result[30] = (decrypt == 1'b1) ? k_r12[26:26] : k_r12[34:34];
  result[29] = (decrypt == 1'b1) ? k_r12[25:25] : k_r12[33:33];
  result[28] = (decrypt == 1'b1) ? k_r12[19:19] : k_r12[27:27];
  result[27] = (decrypt == 1'b1) ? k_r12[20:20] : k_r12[53:53];
  result[26] = (decrypt == 1'b1) ? k_r12[53:53] : k_r12[4:4];
  result[25] = (decrypt == 1'b1) ? k_r12[4:4] : k_r12[12:12];
  result[24] = (decrypt == 1'b1) ? k_r12[41:41] : k_r12[17:17];
  result[23] = (decrypt == 1'b1) ? k_r12[2:2] : k_r12[8:8];
  result[22] = (decrypt == 1'b1) ? k_r12[52:52] : k_r12[30:30];
  result[21] = (decrypt == 1'b1) ? k_r12[42:42] : k_r12[52:52];
  result[20] = (decrypt == 1'b1) ? k_r12[29:29] : k_r12[35:35];
  result[19] = (decrypt == 1'b1) ? k_r12[44:44] : k_r12[50:50];
  result[18] = (decrypt == 1'b1) ? k_r12[14:14] : k_r12[51:51];
  result[17] = (decrypt == 1'b1) ? k_r12[35:35] : k_r12[45:45];
  result[16] = (decrypt == 1'b1) ? k_r12[50:50] : k_r12[1:1];
  result[15] = (decrypt == 1'b1) ? k_r12[45:45] : k_r12[23:23];
  result[14] = (decrypt == 1'b1) ? k_r12[30:30] : k_r12[36:36];
  result[13] = (decrypt == 1'b1) ? k_r12[1:1] : k_r12[7:7];
  result[12] = (decrypt == 1'b1) ? k_r12[51:51] : k_r12[2:2];
  result[11] = (decrypt == 1'b1) ? k_r12[23:23] : k_r12[29:29];
  result[10] = (decrypt == 1'b1) ? k_r12[31:31] : k_r12[9:9];
  result[9] = (decrypt == 1'b1) ? k_r12[43:43] : k_r12[49:49];
  result[8] = (decrypt == 1'b1) ? k_r12[21:21] : k_r12[31:31];
  result[7] = (decrypt == 1'b1) ? k_r12[8:8] : k_r12[14:14];
  result[6] = (decrypt == 1'b1) ? k_r12[0:0] : k_r12[37:37];
  result[5] = (decrypt == 1'b1) ? k_r12[37:37] : k_r12[43:43];
  result[4] = (decrypt == 1'b1) ? k_r12[9:9] : k_r12[15:15];
  result[3] = (decrypt == 1'b1) ? k_r12[38:38] : k_r12[16:16];
  result[2] = (decrypt == 1'b1) ? k_r12[22:22] : k_r12[28:28];
  result[1] = (decrypt == 1'b1) ? k_r12[28:28] : k_r12[38:38];
  result[0] = (decrypt == 1'b1) ? k_r12[49:49] : k_r12[0:0];
  k14 = result;
endmethod: k14

method Bit#(48) k13(decrypt);
  Bit#(48) result;
  result[47] = (decrypt == 1'b1) ? k_r11[25:25] : k_r11[5:5];
  result[46] = (decrypt == 1'b1) ? k_r11[46:46] : k_r11[26:26];
  result[45] = (decrypt == 1'b1) ? k_r11[4:4] : k_r11[41:41];
  result[44] = (decrypt == 1'b1) ? k_r11[13:13] : k_r11[18:18];
  result[43] = (decrypt == 1'b1) ? k_r11[48:48] : k_r11[53:53];
  result[42] = (decrypt == 1'b1) ? k_r11[19:19] : k_r11[24:24];
  result[41] = (decrypt == 1'b1) ? k_r11[5:5] : k_r11[10:10];
  result[40] = (decrypt == 1'b1) ? k_r11[41:41] : k_r11[46:46];
  result[39] = (decrypt == 1'b1) ? k_r11[32:32] : k_r11[12:12];
  result[38] = (decrypt == 1'b1) ? k_r11[26:26] : k_r11[6:6];
  result[37] = (decrypt == 1'b1) ? k_r11[17:17] : k_r11[54:54];
  result[36] = (decrypt == 1'b1) ? k_r11[54:54] : k_r11[34:34];
  result[35] = (decrypt == 1'b1) ? k_r11[6:6] : k_r11[11:11];
  result[34] = (decrypt == 1'b1) ? k_r11[3:3] : k_r11[40:40];
  result[33] = (decrypt == 1'b1) ? k_r11[11:11] : k_r11[48:48];
  result[32] = (decrypt == 1'b1) ? k_r11[12:12] : k_r11[17:17];
  result[31] = (decrypt == 1'b1) ? k_r11[27:27] : k_r11[32:32];
  result[30] = (decrypt == 1'b1) ? k_r11[40:40] : k_r11[20:20];
  result[29] = (decrypt == 1'b1) ? k_r11[39:39] : k_r11[19:19];
  result[28] = (decrypt == 1'b1) ? k_r11[33:33] : k_r11[13:13];
  result[27] = (decrypt == 1'b1) ? k_r11[34:34] : k_r11[39:39];
  result[26] = (decrypt == 1'b1) ? k_r11[10:10] : k_r11[47:47];
  result[25] = (decrypt == 1'b1) ? k_r11[18:18] : k_r11[55:55];
  result[24] = (decrypt == 1'b1) ? k_r11[55:55] : k_r11[3:3];
  result[23] = (decrypt == 1'b1) ? k_r11[16:16] : k_r11[49:49];
  result[22] = (decrypt == 1'b1) ? k_r11[7:7] : k_r11[16:16];
  result[21] = (decrypt == 1'b1) ? k_r11[1:1] : k_r11[38:38];
  result[20] = (decrypt == 1'b1) ? k_r11[43:43] : k_r11[21:21];
  result[19] = (decrypt == 1'b1) ? k_r11[31:31] : k_r11[36:36];
  result[18] = (decrypt == 1'b1) ? k_r11[28:28] : k_r11[37:37];
  result[17] = (decrypt == 1'b1) ? k_r11[49:49] : k_r11[31:31];
  result[16] = (decrypt == 1'b1) ? k_r11[9:9] : k_r11[42:42];
  result[15] = (decrypt == 1'b1) ? k_r11[0:0] : k_r11[9:9];
  result[14] = (decrypt == 1'b1) ? k_r11[44:44] : k_r11[22:22];
  result[13] = (decrypt == 1'b1) ? k_r11[15:15] : k_r11[52:52];
  result[12] = (decrypt == 1'b1) ? k_r11[38:38] : k_r11[43:43];
  result[11] = (decrypt == 1'b1) ? k_r11[37:37] : k_r11[15:15];
  result[10] = (decrypt == 1'b1) ? k_r11[45:45] : k_r11[50:50];
  result[9] = (decrypt == 1'b1) ? k_r11[2:2] : k_r11[35:35];
  result[8] = (decrypt == 1'b1) ? k_r11[35:35] : k_r11[44:44];
  result[7] = (decrypt == 1'b1) ? k_r11[22:22] : k_r11[0:0];
  result[6] = (decrypt == 1'b1) ? k_r11[14:14] : k_r11[23:23];
  result[5] = (decrypt == 1'b1) ? k_r11[51:51] : k_r11[29:29];
  result[4] = (decrypt == 1'b1) ? k_r11[23:23] : k_r11[1:1];
  result[3] = (decrypt == 1'b1) ? k_r11[52:52] : k_r11[2:2];
  result[2] = (decrypt == 1'b1) ? k_r11[36:36] : k_r11[14:14];
  result[1] = (decrypt == 1'b1) ? k_r11[42:42] : k_r11[51:51];
  result[0] = (decrypt == 1'b1) ? k_r11[8:8] : k_r11[45:45];
  k13 = result;
endmethod: k13

method Bit#(48) k12(decrypt);
Bit#(48) result;
  result[47] = (decrypt == 1'b1) ? k_r10[39:39] : k_r10[48:48];
  result[46] = (decrypt == 1'b1) ? k_r10[3:3] : k_r10[12:12];
  result[45] = (decrypt == 1'b1) ? k_r10[18:18] : k_r10[27:27];
  result[44] = (decrypt == 1'b1) ? k_r10[27:27] : k_r10[4:4];
  result[43] = (decrypt == 1'b1) ? k_r10[5:5] : k_r10[39:39];
  result[42] = (decrypt == 1'b1) ? k_r10[33:33] : k_r10[10:10];
  result[41] = (decrypt == 1'b1) ? k_r10[19:19] : k_r10[53:53];
  result[40] = (decrypt == 1'b1) ? k_r10[55:55] : k_r10[32:32];
  result[39] = (decrypt == 1'b1) ? k_r10[46:46] : k_r10[55:55];
  result[38] = (decrypt == 1'b1) ? k_r10[40:40] : k_r10[17:17];
  result[37] = (decrypt == 1'b1) ? k_r10[6:6] : k_r10[40:40];
  result[36] = (decrypt == 1'b1) ? k_r10[11:11] : k_r10[20:20];
  result[35] = (decrypt == 1'b1) ? k_r10[20:20] : k_r10[54:54];
  result[34] = (decrypt == 1'b1) ? k_r10[17:17] : k_r10[26:26];
  result[33] = (decrypt == 1'b1) ? k_r10[25:25] : k_r10[34:34];
  result[32] = (decrypt == 1'b1) ? k_r10[26:26] : k_r10[3:3];
  result[31] = (decrypt == 1'b1) ? k_r10[41:41] : k_r10[18:18];
  result[30] = (decrypt == 1'b1) ? k_r10[54:54] : k_r10[6:6];
  result[29] = (decrypt == 1'b1) ? k_r10[53:53] : k_r10[5:5];
  result[28] = (decrypt == 1'b1) ? k_r10[47:47] : k_r10[24:24];
  result[27] = (decrypt == 1'b1) ? k_r10[48:48] : k_r10[25:25];
  result[26] = (decrypt == 1'b1) ? k_r10[24:24] : k_r10[33:33];
  result[25] = (decrypt == 1'b1) ? k_r10[32:32] : k_r10[41:41];
  result[24] = (decrypt == 1'b1) ? k_r10[12:12] : k_r10[46:46];
  result[23] = (decrypt == 1'b1) ? k_r10[30:30] : k_r10[35:35];
  result[22] = (decrypt == 1'b1) ? k_r10[21:21] : k_r10[2:2];
  result[21] = (decrypt == 1'b1) ? k_r10[15:15] : k_r10[51:51];
  result[20] = (decrypt == 1'b1) ? k_r10[2:2] : k_r10[7:7];
  result[19] = (decrypt == 1'b1) ? k_r10[45:45] : k_r10[22:22];
  result[18] = (decrypt == 1'b1) ? k_r10[42:42] : k_r10[23:23];
  result[17] = (decrypt == 1'b1) ? k_r10[8:8] : k_r10[44:44];
  result[16] = (decrypt == 1'b1) ? k_r10[23:23] : k_r10[28:28];
  result[15] = (decrypt == 1'b1) ? k_r10[14:14] : k_r10[50:50];
  result[14] = (decrypt == 1'b1) ? k_r10[31:31] : k_r10[8:8];
  result[13] = (decrypt == 1'b1) ? k_r10[29:29] : k_r10[38:38];
  result[12] = (decrypt == 1'b1) ? k_r10[52:52] : k_r10[29:29];
  result[11] = (decrypt == 1'b1) ? k_r10[51:51] : k_r10[1:1];
  result[10] = (decrypt == 1'b1) ? k_r10[0:0] : k_r10[36:36];
  result[9] = (decrypt == 1'b1) ? k_r10[16:16] : k_r10[21:21];
  result[8] = (decrypt == 1'b1) ? k_r10[49:49] : k_r10[30:30];
  result[7] = (decrypt == 1'b1) ? k_r10[36:36] : k_r10[45:45];
  result[6] = (decrypt == 1'b1) ? k_r10[28:28] : k_r10[9:9];
  result[5] = (decrypt == 1'b1) ? k_r10[38:38] : k_r10[15:15];
  result[4] = (decrypt == 1'b1) ? k_r10[37:37] : k_r10[42:42];
  result[3] = (decrypt == 1'b1) ? k_r10[7:7] : k_r10[43:43];
  result[2] = (decrypt == 1'b1) ? k_r10[50:50] : k_r10[0:0];
  result[1] = (decrypt == 1'b1) ? k_r10[1:1] : k_r10[37:37];
  result[0] = (decrypt == 1'b1) ? k_r10[22:22] : k_r10[31:31];
  k12 = result;
endmethod: k12


method Bit#(48) k11(decrypt);
  Bit#(48) result;
  result[47] = (decrypt == 1'b1) ? k_r9[53:53] : k_r9[34:34];
  result[46] = (decrypt == 1'b1) ? k_r9[17:17] : k_r9[55:55];
  result[45] = (decrypt == 1'b1) ? k_r9[32:32] : k_r9[13:13];
  result[44] = (decrypt == 1'b1) ? k_r9[41:41] : k_r9[47:47];
  result[43] = (decrypt == 1'b1) ? k_r9[19:19] : k_r9[25:25];
  result[42] = (decrypt == 1'b1) ? k_r9[47:47] : k_r9[53:53];
  result[41] = (decrypt == 1'b1) ? k_r9[33:33] : k_r9[39:39];
  result[40] = (decrypt == 1'b1) ? k_r9[12:12] : k_r9[18:18];
  result[39] = (decrypt == 1'b1) ? k_r9[3:3] : k_r9[41:41];
  result[38] = (decrypt == 1'b1) ? k_r9[54:54] : k_r9[3:3];
  result[37] = (decrypt == 1'b1) ? k_r9[20:20] : k_r9[26:26];
  result[36] = (decrypt == 1'b1) ? k_r9[25:25] : k_r9[6:6];
  result[35] = (decrypt == 1'b1) ? k_r9[34:34] : k_r9[40:40];
  result[34] = (decrypt == 1'b1) ? k_r9[6:6] : k_r9[12:12];
  result[33] = (decrypt == 1'b1) ? k_r9[39:39] : k_r9[20:20];
  result[32] = (decrypt == 1'b1) ? k_r9[40:40] : k_r9[46:46];
  result[31] = (decrypt == 1'b1) ? k_r9[55:55] : k_r9[4:4];
  result[30] = (decrypt == 1'b1) ? k_r9[11:11] : k_r9[17:17];
  result[29] = (decrypt == 1'b1) ? k_r9[10:10] : k_r9[48:48];
  result[28] = (decrypt == 1'b1) ? k_r9[4:4] : k_r9[10:10];
  result[27] = (decrypt == 1'b1) ? k_r9[5:5] : k_r9[11:11];
  result[26] = (decrypt == 1'b1) ? k_r9[13:13] : k_r9[19:19];
  result[25] = (decrypt == 1'b1) ? k_r9[46:46] : k_r9[27:27];
  result[24] = (decrypt == 1'b1) ? k_r9[26:26] : k_r9[32:32];
  result[23] = (decrypt == 1'b1) ? k_r9[44:44] : k_r9[21:21];
  result[22] = (decrypt == 1'b1) ? k_r9[35:35] : k_r9[43:43];
  result[21] = (decrypt == 1'b1) ? k_r9[29:29] : k_r9[37:37];
  result[20] = (decrypt == 1'b1) ? k_r9[16:16] : k_r9[52:52];
  result[19] = (decrypt == 1'b1) ? k_r9[0:0] : k_r9[8:8];
  result[18] = (decrypt == 1'b1) ? k_r9[1:1] : k_r9[9:9];
  result[17] = (decrypt == 1'b1) ? k_r9[22:22] : k_r9[30:30];
  result[16] = (decrypt == 1'b1) ? k_r9[37:37] : k_r9[14:14];
  result[15] = (decrypt == 1'b1) ? k_r9[28:28] : k_r9[36:36];
  result[14] = (decrypt == 1'b1) ? k_r9[45:45] : k_r9[49:49];
  result[13] = (decrypt == 1'b1) ? k_r9[43:43] : k_r9[51:51];
  result[12] = (decrypt == 1'b1) ? k_r9[7:7] : k_r9[15:15];
  result[11] = (decrypt == 1'b1) ? k_r9[38:38] : k_r9[42:42];
  result[10] = (decrypt == 1'b1) ? k_r9[14:14] : k_r9[22:22];
  result[9] = (decrypt == 1'b1) ? k_r9[30:30] : k_r9[7:7];
  result[8] = (decrypt == 1'b1) ? k_r9[8:8] : k_r9[16:16];
  result[7] = (decrypt == 1'b1) ? k_r9[50:50] : k_r9[31:31];
  result[6] = (decrypt == 1'b1) ? k_r9[42:42] : k_r9[50:50];
  result[5] = (decrypt == 1'b1) ? k_r9[52:52] : k_r9[1:1];
  result[4] = (decrypt == 1'b1) ? k_r9[51:51] : k_r9[28:28];
  result[3] = (decrypt == 1'b1) ? k_r9[21:21] : k_r9[29:29];
  result[2] = (decrypt == 1'b1) ? k_r9[9:9] : k_r9[45:45];
  result[1] = (decrypt == 1'b1) ? k_r9[15:15] : k_r9[23:23];
  result[0] = (decrypt == 1'b1) ? k_r9[36:36] : k_r9[44:44];
  k11 = result;
endmethod: k11

method Bit#(48) k10(decrypt);
  Bit#(48) result;
  result[47] = (decrypt == 1'b1) ? k_r8[10:10] : k_r8[20:20];
  result[46] = (decrypt == 1'b1) ? k_r8[6:6] : k_r8[41:41];
  result[45] = (decrypt == 1'b1) ? k_r8[46:46] : k_r8[24:24];
  result[44] = (decrypt == 1'b1) ? k_r8[55:55] : k_r8[33:33];
  result[43] = (decrypt == 1'b1) ? k_r8[33:33] : k_r8[11:11];
  result[42] = (decrypt == 1'b1) ? k_r8[4:4] : k_r8[39:39];
  result[41] = (decrypt == 1'b1) ? k_r8[47:47] : k_r8[25:25];
  result[40] = (decrypt == 1'b1) ? k_r8[26:26] : k_r8[4:4];
  result[39] = (decrypt == 1'b1) ? k_r8[17:17] : k_r8[27:27];
  result[38] = (decrypt == 1'b1) ? k_r8[11:11] : k_r8[46:46];
  result[37] = (decrypt == 1'b1) ? k_r8[34:34] : k_r8[12:12];
  result[36] = (decrypt == 1'b1) ? k_r8[39:39] : k_r8[17:17];
  result[35] = (decrypt == 1'b1) ? k_r8[48:48] : k_r8[26:26];
  result[34] = (decrypt == 1'b1) ? k_r8[20:20] : k_r8[55:55];
  result[33] = (decrypt == 1'b1) ? k_r8[53:53] : k_r8[6:6];
  result[32] = (decrypt == 1'b1) ? k_r8[54:54] : k_r8[32:32];
  result[31] = (decrypt == 1'b1) ? k_r8[12:12] : k_r8[47:47];
  result[30] = (decrypt == 1'b1) ? k_r8[25:25] : k_r8[3:3];
  result[29] = (decrypt == 1'b1) ? k_r8[24:24] : k_r8[34:34];
  result[28] = (decrypt == 1'b1) ? k_r8[18:18] : k_r8[53:53];
  result[27] = (decrypt == 1'b1) ? k_r8[19:19] : k_r8[54:54];
  result[26] = (decrypt == 1'b1) ? k_r8[27:27] : k_r8[5:5];
  result[25] = (decrypt == 1'b1) ? k_r8[3:3] : k_r8[13:13];
  result[24] = (decrypt == 1'b1) ? k_r8[40:40] : k_r8[18:18];
  result[23] = (decrypt == 1'b1) ? k_r8[31:31] : k_r8[7:7];
  result[22] = (decrypt == 1'b1) ? k_r8[49:49] : k_r8[29:29];
  result[21] = (decrypt == 1'b1) ? k_r8[43:43] : k_r8[23:23];
  result[20] = (decrypt == 1'b1) ? k_r8[30:30] : k_r8[38:38];
  result[19] = (decrypt == 1'b1) ? k_r8[14:14] : k_r8[49:49];
  result[18] = (decrypt == 1'b1) ? k_r8[15:15] : k_r8[50:50];
  result[17] = (decrypt == 1'b1) ? k_r8[36:36] : k_r8[16:16];
  result[16] = (decrypt == 1'b1) ? k_r8[51:51] : k_r8[0:0];
  result[15] = (decrypt == 1'b1) ? k_r8[42:42] : k_r8[22:22];
  result[14] = (decrypt == 1'b1) ? k_r8[0:0] : k_r8[35:35];
  result[13] = (decrypt == 1'b1) ? k_r8[2:2] : k_r8[37:37];
  result[12] = (decrypt == 1'b1) ? k_r8[21:21] : k_r8[1:1];
  result[11] = (decrypt == 1'b1) ? k_r8[52:52] : k_r8[28:28];
  result[10] = (decrypt == 1'b1) ? k_r8[28:28] : k_r8[8:8];
  result[9] = (decrypt == 1'b1) ? k_r8[44:44] : k_r8[52:52];
  result[8] = (decrypt == 1'b1) ? k_r8[22:22] : k_r8[2:2];
  result[7] = (decrypt == 1'b1) ? k_r8[9:9] : k_r8[44:44];
  result[6] = (decrypt == 1'b1) ? k_r8[1:1] : k_r8[36:36];
  result[5] = (decrypt == 1'b1) ? k_r8[7:7] : k_r8[42:42];
  result[4] = (decrypt == 1'b1) ? k_r8[38:38] : k_r8[14:14];
  result[3] = (decrypt == 1'b1) ? k_r8[35:35] : k_r8[15:15];
  result[2] = (decrypt == 1'b1) ? k_r8[23:23] : k_r8[31:31];
  result[1] = (decrypt == 1'b1) ? k_r8[29:29] : k_r8[9:9];
  result[0] = (decrypt == 1'b1) ? k_r8[50:50] : k_r8[30:30];
  k10 = result;
endmethod: k10

method Bit#(48) k9(decrypt);
 Bit#(48) result;
  result[47] = (decrypt == 1'b1) ? k_r7[24:24] : k_r7[6:6];
  result[46] = (decrypt == 1'b1) ? k_r7[20:20] : k_r7[27:27];
  result[45] = (decrypt == 1'b1) ? k_r7[3:3] : k_r7[10:10];
  result[44] = (decrypt == 1'b1) ? k_r7[12:12] : k_r7[19:19];
  result[43] = (decrypt == 1'b1) ? k_r7[47:47] : k_r7[54:54];
  result[42] = (decrypt == 1'b1) ? k_r7[18:18] : k_r7[25:25];
  result[41] = (decrypt == 1'b1) ? k_r7[4:4] : k_r7[11:11];
  result[40] = (decrypt == 1'b1) ? k_r7[40:40] : k_r7[47:47];
  result[39] = (decrypt == 1'b1) ? k_r7[6:6] : k_r7[13:13];
  result[38] = (decrypt == 1'b1) ? k_r7[25:25] : k_r7[32:32];
  result[37] = (decrypt == 1'b1) ? k_r7[48:48] : k_r7[55:55];
  result[36] = (decrypt == 1'b1) ? k_r7[53:53] : k_r7[3:3];
  result[35] = (decrypt == 1'b1) ? k_r7[5:5] : k_r7[12:12];
  result[34] = (decrypt == 1'b1) ? k_r7[34:34] : k_r7[41:41];
  result[33] = (decrypt == 1'b1) ? k_r7[10:10] : k_r7[17:17];
  result[32] = (decrypt == 1'b1) ? k_r7[11:11] : k_r7[18:18];
  result[31] = (decrypt == 1'b1) ? k_r7[26:26] : k_r7[33:33];
  result[30] = (decrypt == 1'b1) ? k_r7[39:39] : k_r7[46:46];
  result[29] = (decrypt == 1'b1) ? k_r7[13:13] : k_r7[20:20];
  result[28] = (decrypt == 1'b1) ? k_r7[32:32] : k_r7[39:39];
  result[27] = (decrypt == 1'b1) ? k_r7[33:33] : k_r7[40:40];
  result[26] = (decrypt == 1'b1) ? k_r7[41:41] : k_r7[48:48];
  result[25] = (decrypt == 1'b1) ? k_r7[17:17] : k_r7[24:24];
  result[24] = (decrypt == 1'b1) ? k_r7[54:54] : k_r7[4:4];
  result[23] = (decrypt == 1'b1) ? k_r7[45:45] : k_r7[52:52];
  result[22] = (decrypt == 1'b1) ? k_r7[8:8] : k_r7[15:15];
  result[21] = (decrypt == 1'b1) ? k_r7[2:2] : k_r7[9:9];
  result[20] = (decrypt == 1'b1) ? k_r7[44:44] : k_r7[51:51];
  result[19] = (decrypt == 1'b1) ? k_r7[28:28] : k_r7[35:35];
  result[18] = (decrypt == 1'b1) ? k_r7[29:29] : k_r7[36:36];
  result[17] = (decrypt == 1'b1) ? k_r7[50:50] : k_r7[2:2];
  result[16] = (decrypt == 1'b1) ? k_r7[38:38] : k_r7[45:45];
  result[15] = (decrypt == 1'b1) ? k_r7[1:1] : k_r7[8:8];
  result[14] = (decrypt == 1'b1) ? k_r7[14:14] : k_r7[21:21];
  result[13] = (decrypt == 1'b1) ? k_r7[16:16] : k_r7[23:23];
  result[12] = (decrypt == 1'b1) ? k_r7[35:35] : k_r7[42:42];
  result[11] = (decrypt == 1'b1) ? k_r7[7:7] : k_r7[14:14];
  result[10] = (decrypt == 1'b1) ? k_r7[42:42] : k_r7[49:49];
  result[9] = (decrypt == 1'b1) ? k_r7[31:31] : k_r7[38:38];
  result[8] = (decrypt == 1'b1) ? k_r7[36:36] : k_r7[43:43];
  result[7] = (decrypt == 1'b1) ? k_r7[23:23] : k_r7[30:30];
  result[6] = (decrypt == 1'b1) ? k_r7[15:15] : k_r7[22:22];
  result[5] = (decrypt == 1'b1) ? k_r7[21:21] : k_r7[28:28];
  result[4] = (decrypt == 1'b1) ? k_r7[52:52] : k_r7[0:0];
  result[3] = (decrypt == 1'b1) ? k_r7[49:49] : k_r7[1:1];
  result[2] = (decrypt == 1'b1) ? k_r7[37:37] : k_r7[44:44];
  result[1] = (decrypt == 1'b1) ? k_r7[43:43] : k_r7[50:50];
  result[0] = (decrypt == 1'b1) ? k_r7[9:9] : k_r7[16:16];
  k9 = result;
endmethod: k9

method Bit#(48) k8(decrypt);
  Bit#(48) result;
  result[47] = (decrypt == 1'b1) ? k_r6[6:6] : k_r6[24:24];
  result[46] = (decrypt == 1'b1) ? k_r6[27:27] : k_r6[20:20];
  result[45] = (decrypt == 1'b1) ? k_r6[10:10] : k_r6[3:3];
  result[44] = (decrypt == 1'b1) ? k_r6[19:19] : k_r6[12:12];
  result[43] = (decrypt == 1'b1) ? k_r6[54:54] : k_r6[47:47];
  result[42] = (decrypt == 1'b1) ? k_r6[25:25] : k_r6[18:18];
  result[41] = (decrypt == 1'b1) ? k_r6[11:11] : k_r6[4:4];
  result[40] = (decrypt == 1'b1) ? k_r6[47:47] : k_r6[40:40];
  result[39] = (decrypt == 1'b1) ? k_r6[13:13] : k_r6[6:6];
  result[38] = (decrypt == 1'b1) ? k_r6[32:32] : k_r6[25:25];
  result[37] = (decrypt == 1'b1) ? k_r6[55:55] : k_r6[48:48];
  result[36] = (decrypt == 1'b1) ? k_r6[3:3] : k_r6[53:53];
  result[35] = (decrypt == 1'b1) ? k_r6[12:12] : k_r6[5:5];
  result[34] = (decrypt == 1'b1) ? k_r6[41:41] : k_r6[34:34];
  result[33] = (decrypt == 1'b1) ? k_r6[17:17] : k_r6[10:10];
  result[32] = (decrypt == 1'b1) ? k_r6[18:18] : k_r6[11:11];
  result[31] = (decrypt == 1'b1) ? k_r6[33:33] : k_r6[26:26];
  result[30] = (decrypt == 1'b1) ? k_r6[46:46] : k_r6[39:39];
  result[29] = (decrypt == 1'b1) ? k_r6[20:20] : k_r6[13:13];
  result[28] = (decrypt == 1'b1) ? k_r6[39:39] : k_r6[32:32];
  result[27] = (decrypt == 1'b1) ? k_r6[40:40] : k_r6[33:33];
  result[26] = (decrypt == 1'b1) ? k_r6[48:48] : k_r6[41:41];
  result[25] = (decrypt == 1'b1) ? k_r6[24:24] : k_r6[17:17];
  result[24] = (decrypt == 1'b1) ? k_r6[4:4] : k_r6[54:54];
  result[23] = (decrypt == 1'b1) ? k_r6[52:52] : k_r6[45:45];
  result[22] = (decrypt == 1'b1) ? k_r6[15:15] : k_r6[8:8];
  result[21] = (decrypt == 1'b1) ? k_r6[9:9] : k_r6[2:2];
  result[20] = (decrypt == 1'b1) ? k_r6[51:51] : k_r6[44:44];
  result[19] = (decrypt == 1'b1) ? k_r6[35:35] : k_r6[28:28];
  result[18] = (decrypt == 1'b1) ? k_r6[36:36] : k_r6[29:29];
  result[17] = (decrypt == 1'b1) ? k_r6[2:2] : k_r6[50:50];
  result[16] = (decrypt == 1'b1) ? k_r6[45:45] : k_r6[38:38];
  result[15] = (decrypt == 1'b1) ? k_r6[8:8] : k_r6[1:1];
  result[14] = (decrypt == 1'b1) ? k_r6[21:21] : k_r6[14:14];
  result[13] = (decrypt == 1'b1) ? k_r6[23:23] : k_r6[16:16];
  result[12] = (decrypt == 1'b1) ? k_r6[42:42] : k_r6[35:35];
  result[11] = (decrypt == 1'b1) ? k_r6[14:14] : k_r6[7:7];
  result[10] = (decrypt == 1'b1) ? k_r6[49:49] : k_r6[42:42];
  result[9] = (decrypt == 1'b1) ? k_r6[38:38] : k_r6[31:31];
  result[8] = (decrypt == 1'b1) ? k_r6[43:43] : k_r6[36:36];
  result[7] = (decrypt == 1'b1) ? k_r6[30:30] : k_r6[23:23];
  result[6] = (decrypt == 1'b1) ? k_r6[22:22] : k_r6[15:15];
  result[5] = (decrypt == 1'b1) ? k_r6[28:28] : k_r6[21:21];
  result[4] = (decrypt == 1'b1) ? k_r6[0:0] : k_r6[52:52];
  result[3] = (decrypt == 1'b1) ? k_r6[1:1] : k_r6[49:49];
  result[2] = (decrypt == 1'b1) ? k_r6[44:44] : k_r6[37:37];
  result[1] = (decrypt == 1'b1) ? k_r6[50:50] : k_r6[43:43];
  result[0] = (decrypt == 1'b1) ? k_r6[16:16] : k_r6[9:9];
  k8 = result;
endmethod: k8

method Bit#(48) k7(decrypt);
  Bit#(48) result;
  result[47] = (decrypt == 1'b1) ? k_r5[20:20] : k_r5[10:10];
  result[46] = (decrypt == 1'b1) ? k_r5[41:41] : k_r5[6:6];
  result[45] = (decrypt == 1'b1) ? k_r5[24:24] : k_r5[46:46];
  result[44] = (decrypt == 1'b1) ? k_r5[33:33] : k_r5[55:55];
  result[43] = (decrypt == 1'b1) ? k_r5[11:11] : k_r5[33:33];
  result[42] = (decrypt == 1'b1) ? k_r5[39:39] : k_r5[4:4];
  result[41] = (decrypt == 1'b1) ? k_r5[25:25] : k_r5[47:47];
  result[40] = (decrypt == 1'b1) ? k_r5[4:4] : k_r5[26:26];
  result[39] = (decrypt == 1'b1) ? k_r5[27:27] : k_r5[17:17];
  result[38] = (decrypt == 1'b1) ? k_r5[46:46] : k_r5[11:11];
  result[37] = (decrypt == 1'b1) ? k_r5[12:12] : k_r5[34:34];
  result[36] = (decrypt == 1'b1) ? k_r5[17:17] : k_r5[39:39];
  result[35] = (decrypt == 1'b1) ? k_r5[26:26] : k_r5[48:48];
  result[34] = (decrypt == 1'b1) ? k_r5[55:55] : k_r5[20:20];
  result[33] = (decrypt == 1'b1) ? k_r5[6:6] : k_r5[53:53];
  result[32] = (decrypt == 1'b1) ? k_r5[32:32] : k_r5[54:54];
  result[31] = (decrypt == 1'b1) ? k_r5[47:47] : k_r5[12:12];
  result[30] = (decrypt == 1'b1) ? k_r5[3:3] : k_r5[25:25];
  result[29] = (decrypt == 1'b1) ? k_r5[34:34] : k_r5[24:24];
  result[28] = (decrypt == 1'b1) ? k_r5[53:53] : k_r5[18:18];
  result[27] = (decrypt == 1'b1) ? k_r5[54:54] : k_r5[19:19];
  result[26] = (decrypt == 1'b1) ? k_r5[5:5] : k_r5[27:27];
  result[25] = (decrypt == 1'b1) ? k_r5[13:13] : k_r5[3:3];
  result[24] = (decrypt == 1'b1) ? k_r5[18:18] : k_r5[40:40];
  result[23] = (decrypt == 1'b1) ? k_r5[7:7] : k_r5[31:31];
  result[22] = (decrypt == 1'b1) ? k_r5[29:29] : k_r5[49:49];
  result[21] = (decrypt == 1'b1) ? k_r5[23:23] : k_r5[43:43];
  result[20] = (decrypt == 1'b1) ? k_r5[38:38] : k_r5[30:30];
  result[19] = (decrypt == 1'b1) ? k_r5[49:49] : k_r5[14:14];
  result[18] = (decrypt == 1'b1) ? k_r5[50:50] : k_r5[15:15];
  result[17] = (decrypt == 1'b1) ? k_r5[16:16] : k_r5[36:36];
  result[16] = (decrypt == 1'b1) ? k_r5[0:0] : k_r5[51:51];
  result[15] = (decrypt == 1'b1) ? k_r5[22:22] : k_r5[42:42];
  result[14] = (decrypt == 1'b1) ? k_r5[35:35] : k_r5[0:0];
  result[13] = (decrypt == 1'b1) ? k_r5[37:37] : k_r5[2:2];
  result[12] = (decrypt == 1'b1) ? k_r5[1:1] : k_r5[21:21];
  result[11] = (decrypt == 1'b1) ? k_r5[28:28] : k_r5[52:52];
  result[10] = (decrypt == 1'b1) ? k_r5[8:8] : k_r5[28:28];
  result[9] = (decrypt == 1'b1) ? k_r5[52:52] : k_r5[44:44];
  result[8] = (decrypt == 1'b1) ? k_r5[2:2] : k_r5[22:22];
  result[7] = (decrypt == 1'b1) ? k_r5[44:44] : k_r5[9:9];
  result[6] = (decrypt == 1'b1) ? k_r5[36:36] : k_r5[1:1];
  result[5] = (decrypt == 1'b1) ? k_r5[42:42] : k_r5[7:7];
  result[4] = (decrypt == 1'b1) ? k_r5[14:14] : k_r5[38:38];
  result[3] = (decrypt == 1'b1) ? k_r5[15:15] : k_r5[35:35];
  result[2] = (decrypt == 1'b1) ? k_r5[31:31] : k_r5[23:23];
  result[1] = (decrypt == 1'b1) ? k_r5[9:9] : k_r5[29:29];
  result[0] = (decrypt == 1'b1) ? k_r5[30:30] : k_r5[50:50];
  k7 = result;
endmethod: k7

method Bit#(48) k6(decrypt);
  Bit#(48) result;
  result[47] = (decrypt == 1'b1) ? k_r4[34:34] : k_r4[53:53];
  result[46] = (decrypt == 1'b1) ? k_r4[55:55] : k_r4[17:17];
  result[45] = (decrypt == 1'b1) ? k_r4[13:13] : k_r4[32:32];
  result[44] = (decrypt == 1'b1) ? k_r4[47:47] : k_r4[41:41];
  result[43] = (decrypt == 1'b1) ? k_r4[25:25] : k_r4[19:19];
  result[42] = (decrypt == 1'b1) ? k_r4[53:53] : k_r4[47:47];
  result[41] = (decrypt == 1'b1) ? k_r4[39:39] : k_r4[33:33];
  result[40] = (decrypt == 1'b1) ? k_r4[18:18] : k_r4[12:12];
  result[39] = (decrypt == 1'b1) ? k_r4[41:41] : k_r4[3:3];
  result[38] = (decrypt == 1'b1) ? k_r4[3:3] : k_r4[54:54];
  result[37] = (decrypt == 1'b1) ? k_r4[26:26] : k_r4[20:20];
  result[36] = (decrypt == 1'b1) ? k_r4[6:6] : k_r4[25:25];
  result[35] = (decrypt == 1'b1) ? k_r4[40:40] : k_r4[34:34];
  result[34] = (decrypt == 1'b1) ? k_r4[12:12] : k_r4[6:6];
  result[33] = (decrypt == 1'b1) ? k_r4[20:20] : k_r4[39:39];
  result[32] = (decrypt == 1'b1) ? k_r4[46:46] : k_r4[40:40];
  result[31] = (decrypt == 1'b1) ? k_r4[4:4] : k_r4[55:55];
  result[30] = (decrypt == 1'b1) ? k_r4[17:17] : k_r4[11:11];
  result[29] = (decrypt == 1'b1) ? k_r4[48:48] : k_r4[10:10];
  result[28] = (decrypt == 1'b1) ? k_r4[10:10] : k_r4[4:4];
  result[27] = (decrypt == 1'b1) ? k_r4[11:11] : k_r4[5:5];
  result[26] = (decrypt == 1'b1) ? k_r4[19:19] : k_r4[13:13];
  result[25] = (decrypt == 1'b1) ? k_r4[27:27] : k_r4[46:46];
  result[24] = (decrypt == 1'b1) ? k_r4[32:32] : k_r4[26:26];
  result[23] = (decrypt == 1'b1) ? k_r4[21:21] : k_r4[44:44];
  result[22] = (decrypt == 1'b1) ? k_r4[43:43] : k_r4[35:35];
  result[21] = (decrypt == 1'b1) ? k_r4[37:37] : k_r4[29:29];
  result[20] = (decrypt == 1'b1) ? k_r4[52:52] : k_r4[16:16];
  result[19] = (decrypt == 1'b1) ? k_r4[8:8] : k_r4[0:0];
  result[18] = (decrypt == 1'b1) ? k_r4[9:9] : k_r4[1:1];
  result[17] = (decrypt == 1'b1) ? k_r4[30:30] : k_r4[22:22];
  result[16] = (decrypt == 1'b1) ? k_r4[14:14] : k_r4[37:37];
  result[15] = (decrypt == 1'b1) ? k_r4[36:36] : k_r4[28:28];
  result[14] = (decrypt == 1'b1) ? k_r4[49:49] : k_r4[45:45];
  result[13] = (decrypt == 1'b1) ? k_r4[51:51] : k_r4[43:43];
  result[12] = (decrypt == 1'b1) ? k_r4[15:15] : k_r4[7:7];
  result[11] = (decrypt == 1'b1) ? k_r4[42:42] : k_r4[38:38];
  result[10] = (decrypt == 1'b1) ? k_r4[22:22] : k_r4[14:14];
  result[9] = (decrypt == 1'b1) ? k_r4[7:7] : k_r4[30:30];
  result[8] = (decrypt == 1'b1) ? k_r4[16:16] : k_r4[8:8];
  result[7] = (decrypt == 1'b1) ? k_r4[31:31] : k_r4[50:50];
  result[6] = (decrypt == 1'b1) ? k_r4[50:50] : k_r4[42:42];
  result[5] = (decrypt == 1'b1) ? k_r4[1:1] : k_r4[52:52];
  result[4] = (decrypt == 1'b1) ? k_r4[28:28] : k_r4[51:51];
  result[3] = (decrypt == 1'b1) ? k_r4[29:29] : k_r4[21:21];
  result[2] = (decrypt == 1'b1) ? k_r4[45:45] : k_r4[9:9];
  result[1] = (decrypt == 1'b1) ? k_r4[23:23] : k_r4[15:15];
  result[0] = (decrypt == 1'b1) ? k_r4[44:44] : k_r4[36:36];
  k6 = result;
endmethod: k6

method Bit#(48) k5(decrypt);
  Bit#(48) result;
  result[47] = (decrypt == 1'b1) ? k_r3[48:48] : k_r3[39:39];
  result[46] = (decrypt == 1'b1) ? k_r3[12:12] : k_r3[3:3];
  result[45] = (decrypt == 1'b1) ? k_r3[27:27] : k_r3[18:18];
  result[44] = (decrypt == 1'b1) ? k_r3[4:4] : k_r3[27:27];
  result[43] = (decrypt == 1'b1) ? k_r3[39:39] : k_r3[5:5];
  result[42] = (decrypt == 1'b1) ? k_r3[10:10] : k_r3[33:33];
  result[41] = (decrypt == 1'b1) ? k_r3[53:53] : k_r3[19:19];
  result[40] = (decrypt == 1'b1) ? k_r3[32:32] : k_r3[55:55];
  result[39] = (decrypt == 1'b1) ? k_r3[55:55] : k_r3[46:46];
  result[38] = (decrypt == 1'b1) ? k_r3[17:17] : k_r3[40:40];
  result[37] = (decrypt == 1'b1) ? k_r3[40:40] : k_r3[6:6];
  result[36] = (decrypt == 1'b1) ? k_r3[20:20] : k_r3[11:11];
  result[35] = (decrypt == 1'b1) ? k_r3[54:54] : k_r3[20:20];
  result[34] = (decrypt == 1'b1) ? k_r3[26:26] : k_r3[17:17];
  result[33] = (decrypt == 1'b1) ? k_r3[34:34] : k_r3[25:25];
  result[32] = (decrypt == 1'b1) ? k_r3[3:3] : k_r3[26:26];
  result[31] = (decrypt == 1'b1) ? k_r3[18:18] : k_r3[41:41];
  result[30] = (decrypt == 1'b1) ? k_r3[6:6] : k_r3[54:54];
  result[29] = (decrypt == 1'b1) ? k_r3[5:5] : k_r3[53:53];
  result[28] = (decrypt == 1'b1) ? k_r3[24:24] : k_r3[47:47];
  result[27] = (decrypt == 1'b1) ? k_r3[25:25] : k_r3[48:48];
  result[26] = (decrypt == 1'b1) ? k_r3[33:33] : k_r3[24:24];
  result[25] = (decrypt == 1'b1) ? k_r3[41:41] : k_r3[32:32];
  result[24] = (decrypt == 1'b1) ? k_r3[46:46] : k_r3[12:12];
  result[23] = (decrypt == 1'b1) ? k_r3[35:35] : k_r3[30:30];
  result[22] = (decrypt == 1'b1) ? k_r3[2:2] : k_r3[21:21];
  result[21] = (decrypt == 1'b1) ? k_r3[51:51] : k_r3[15:15];
  result[20] = (decrypt == 1'b1) ? k_r3[7:7] : k_r3[2:2];
  result[19] = (decrypt == 1'b1) ? k_r3[22:22] : k_r3[45:45];
  result[18] = (decrypt == 1'b1) ? k_r3[23:23] : k_r3[42:42];
  result[17] = (decrypt == 1'b1) ? k_r3[44:44] : k_r3[8:8];
  result[16] = (decrypt == 1'b1) ? k_r3[28:28] : k_r3[23:23];
  result[15] = (decrypt == 1'b1) ? k_r3[50:50] : k_r3[14:14];
  result[14] = (decrypt == 1'b1) ? k_r3[8:8] : k_r3[31:31];
  result[13] = (decrypt == 1'b1) ? k_r3[38:38] : k_r3[29:29];
  result[12] = (decrypt == 1'b1) ? k_r3[29:29] : k_r3[52:52];
  result[11] = (decrypt == 1'b1) ? k_r3[1:1] : k_r3[51:51];
  result[10] = (decrypt == 1'b1) ? k_r3[36:36] : k_r3[0:0];
  result[9] = (decrypt == 1'b1) ? k_r3[21:21] : k_r3[16:16];
  result[8] = (decrypt == 1'b1) ? k_r3[30:30] : k_r3[49:49];
  result[7] = (decrypt == 1'b1) ? k_r3[45:45] : k_r3[36:36];
  result[6] = (decrypt == 1'b1) ? k_r3[9:9] : k_r3[28:28];
  result[5] = (decrypt == 1'b1) ? k_r3[15:15] : k_r3[38:38];
  result[4] = (decrypt == 1'b1) ? k_r3[42:42] : k_r3[37:37];
  result[3] = (decrypt == 1'b1) ? k_r3[43:43] : k_r3[7:7];
  result[2] = (decrypt == 1'b1) ? k_r3[0:0] : k_r3[50:50];
  result[1] = (decrypt == 1'b1) ? k_r3[37:37] : k_r3[1:1];
  result[0] = (decrypt == 1'b1) ? k_r3[31:31] : k_r3[22:22];
  k5 = result;
endmethod: k5

method Bit#(48) k4(decrypt);
  Bit#(48) result;
  result[47] = (decrypt == 1'b1) ? k_r2[5:5] : k_r2[25:25];
  result[46] = (decrypt == 1'b1) ? k_r2[26:26] : k_r2[46:46];
  result[45] = (decrypt == 1'b1) ? k_r2[41:41] : k_r2[4:4];
  result[44] = (decrypt == 1'b1) ? k_r2[18:18] : k_r2[13:13];
  result[43] = (decrypt == 1'b1) ? k_r2[53:53] : k_r2[48:48];
  result[42] = (decrypt == 1'b1) ? k_r2[24:24] : k_r2[19:19];
  result[41] = (decrypt == 1'b1) ? k_r2[10:10] : k_r2[5:5];
  result[40] = (decrypt == 1'b1) ? k_r2[46:46] : k_r2[41:41];
  result[39] = (decrypt == 1'b1) ? k_r2[12:12] : k_r2[32:32];
  result[38] = (decrypt == 1'b1) ? k_r2[6:6] : k_r2[26:26];
  result[37] = (decrypt == 1'b1) ? k_r2[54:54] : k_r2[17:17];
  result[36] = (decrypt == 1'b1) ? k_r2[34:34] : k_r2[54:54];
  result[35] = (decrypt == 1'b1) ? k_r2[11:11] : k_r2[6:6];
  result[34] = (decrypt == 1'b1) ? k_r2[40:40] : k_r2[3:3];
  result[33] = (decrypt == 1'b1) ? k_r2[48:48] : k_r2[11:11];
  result[32] = (decrypt == 1'b1) ? k_r2[17:17] : k_r2[12:12];
  result[31] = (decrypt == 1'b1) ? k_r2[32:32] : k_r2[27:27];
  result[30] = (decrypt == 1'b1) ? k_r2[20:20] : k_r2[40:40];
  result[29] = (decrypt == 1'b1) ? k_r2[19:19] : k_r2[39:39];
  result[28] = (decrypt == 1'b1) ? k_r2[13:13] : k_r2[33:33];
  result[27] = (decrypt == 1'b1) ? k_r2[39:39] : k_r2[34:34];
  result[26] = (decrypt == 1'b1) ? k_r2[47:47] : k_r2[10:10];
  result[25] = (decrypt == 1'b1) ? k_r2[55:55] : k_r2[18:18];
  result[24] = (decrypt == 1'b1) ? k_r2[3:3] : k_r2[55:55];
  result[23] = (decrypt == 1'b1) ? k_r2[49:49] : k_r2[16:16];
  result[22] = (decrypt == 1'b1) ? k_r2[16:16] : k_r2[7:7];
  result[21] = (decrypt == 1'b1) ? k_r2[38:38] : k_r2[1:1];
  result[20] = (decrypt == 1'b1) ? k_r2[21:21] : k_r2[43:43];
  result[19] = (decrypt == 1'b1) ? k_r2[36:36] : k_r2[31:31];
  result[18] = (decrypt == 1'b1) ? k_r2[37:37] : k_r2[28:28];
  result[17] = (decrypt == 1'b1) ? k_r2[31:31] : k_r2[49:49];
  result[16] = (decrypt == 1'b1) ? k_r2[42:42] : k_r2[9:9];
  result[15] = (decrypt == 1'b1) ? k_r2[9:9] : k_r2[0:0];
  result[14] = (decrypt == 1'b1) ? k_r2[22:22] : k_r2[44:44];
  result[13] = (decrypt == 1'b1) ? k_r2[52:52] : k_r2[15:15];
  result[12] = (decrypt == 1'b1) ? k_r2[43:43] : k_r2[38:38];
  result[11] = (decrypt == 1'b1) ? k_r2[15:15] : k_r2[37:37];
  result[10] = (decrypt == 1'b1) ? k_r2[50:50] : k_r2[45:45];
  result[9] = (decrypt == 1'b1) ? k_r2[35:35] : k_r2[2:2];
  result[8] = (decrypt == 1'b1) ? k_r2[44:44] : k_r2[35:35];
  result[7] = (decrypt == 1'b1) ? k_r2[0:0] : k_r2[22:22];
  result[6] = (decrypt == 1'b1) ? k_r2[23:23] : k_r2[14:14];
  result[5] = (decrypt == 1'b1) ? k_r2[29:29] : k_r2[51:51];
  result[4] = (decrypt == 1'b1) ? k_r2[1:1] : k_r2[23:23];
  result[3] = (decrypt == 1'b1) ? k_r2[2:2] : k_r2[52:52];
  result[2] = (decrypt == 1'b1) ? k_r2[14:14] : k_r2[36:36];
  result[1] = (decrypt == 1'b1) ? k_r2[51:51] : k_r2[42:42];
  result[0] = (decrypt == 1'b1) ? k_r2[45:45] : k_r2[8:8];
  k4 = result;
endmethod: k4

method Bit#(48) k3(decrypt);
  Bit#(48) result;
  result[47] = (decrypt == 1'b1) ? k_r1[19:19] : k_r1[11:11];
  result[46] = (decrypt == 1'b1) ? k_r1[40:40] : k_r1[32:32];
  result[45] = (decrypt == 1'b1) ? k_r1[55:55] : k_r1[47:47];
  result[44] = (decrypt == 1'b1) ? k_r1[32:32] : k_r1[24:24];
  result[43] = (decrypt == 1'b1) ? k_r1[10:10] : k_r1[34:34];
  result[42] = (decrypt == 1'b1) ? k_r1[13:13] : k_r1[5:5];
  result[41] = (decrypt == 1'b1) ? k_r1[24:24] : k_r1[48:48];
  result[40] = (decrypt == 1'b1) ? k_r1[3:3] : k_r1[27:27];
  result[39] = (decrypt == 1'b1) ? k_r1[26:26] : k_r1[18:18];
  result[38] = (decrypt == 1'b1) ? k_r1[20:20] : k_r1[12:12];
  result[37] = (decrypt == 1'b1) ? k_r1[11:11] : k_r1[3:3];
  result[36] = (decrypt == 1'b1) ? k_r1[48:48] : k_r1[40:40];
  result[35] = (decrypt == 1'b1) ? k_r1[25:25] : k_r1[17:17];
  result[34] = (decrypt == 1'b1) ? k_r1[54:54] : k_r1[46:46];
  result[33] = (decrypt == 1'b1) ? k_r1[5:5] : k_r1[54:54];
  result[32] = (decrypt == 1'b1) ? k_r1[6:6] : k_r1[55:55];
  result[31] = (decrypt == 1'b1) ? k_r1[46:46] : k_r1[13:13];
  result[30] = (decrypt == 1'b1) ? k_r1[34:34] : k_r1[26:26];
  result[29] = (decrypt == 1'b1) ? k_r1[33:33] : k_r1[25:25];
  result[28] = (decrypt == 1'b1) ? k_r1[27:27] : k_r1[19:19];
  result[27] = (decrypt == 1'b1) ? k_r1[53:53] : k_r1[20:20];
  result[26] = (decrypt == 1'b1) ? k_r1[4:4] : k_r1[53:53];
  result[25] = (decrypt == 1'b1) ? k_r1[12:12] : k_r1[4:4];
  result[24] = (decrypt == 1'b1) ? k_r1[17:17] : k_r1[41:41];
  result[23] = (decrypt == 1'b1) ? k_r1[8:8] : k_r1[2:2];
  result[22] = (decrypt == 1'b1) ? k_r1[30:30] : k_r1[52:52];
  result[21] = (decrypt == 1'b1) ? k_r1[52:52] : k_r1[42:42];
  result[20] = (decrypt == 1'b1) ? k_r1[35:35] : k_r1[29:29];
  result[19] = (decrypt == 1'b1) ? k_r1[50:50] : k_r1[44:44];
  result[18] = (decrypt == 1'b1) ? k_r1[51:51] : k_r1[14:14];
  result[17] = (decrypt == 1'b1) ? k_r1[45:45] : k_r1[35:35];
  result[16] = (decrypt == 1'b1) ? k_r1[1:1] : k_r1[50:50];
  result[15] = (decrypt == 1'b1) ? k_r1[23:23] : k_r1[45:45];
  result[14] = (decrypt == 1'b1) ? k_r1[36:36] : k_r1[30:30];
  result[13] = (decrypt == 1'b1) ? k_r1[7:7] : k_r1[1:1];
  result[12] = (decrypt == 1'b1) ? k_r1[2:2] : k_r1[51:51];
  result[11] = (decrypt == 1'b1) ? k_r1[29:29] : k_r1[23:23];
  result[10] = (decrypt == 1'b1) ? k_r1[9:9] : k_r1[31:31];
  result[9] = (decrypt == 1'b1) ? k_r1[49:49] : k_r1[43:43];
  result[8] = (decrypt == 1'b1) ? k_r1[31:31] : k_r1[21:21];
  result[7] = (decrypt == 1'b1) ? k_r1[14:14] : k_r1[8:8];
  result[6] = (decrypt == 1'b1) ? k_r1[37:37] : k_r1[0:0];
  result[5] = (decrypt == 1'b1) ? k_r1[43:43] : k_r1[37:37];
  result[4] = (decrypt == 1'b1) ? k_r1[15:15] : k_r1[9:9];
  result[3] = (decrypt == 1'b1) ? k_r1[16:16] : k_r1[38:38];
  result[2] = (decrypt == 1'b1) ? k_r1[28:28] : k_r1[22:22];
  result[1] = (decrypt == 1'b1) ? k_r1[38:38] : k_r1[28:28];
  result[0] = (decrypt == 1'b1) ? k_r1[0:0] : k_r1[49:49];
  k3 = result;
endmethod: k3

method Bit#(48) k2(decrypt);
  Bit#(48) result;
  result[47] = (decrypt == 1'b1) ? k_r0[33:33] : k_r0[54:54];
  result[46] = (decrypt == 1'b1) ? k_r0[54:54] : k_r0[18:18];
  result[45] = (decrypt == 1'b1) ? k_r0[12:12] : k_r0[33:33];
  result[44] = (decrypt == 1'b1) ? k_r0[46:46] : k_r0[10:10];
  result[43] = (decrypt == 1'b1) ? k_r0[24:24] : k_r0[20:20];
  result[42] = (decrypt == 1'b1) ? k_r0[27:27] : k_r0[48:48];
  result[41] = (decrypt == 1'b1) ? k_r0[13:13] : k_r0[34:34];
  result[40] = (decrypt == 1'b1) ? k_r0[17:17] : k_r0[13:13];
  result[39] = (decrypt == 1'b1) ? k_r0[40:40] : k_r0[4:4];
  result[38] = (decrypt == 1'b1) ? k_r0[34:34] : k_r0[55:55];
  result[37] = (decrypt == 1'b1) ? k_r0[25:25] : k_r0[46:46];
  result[36] = (decrypt == 1'b1) ? k_r0[5:5] : k_r0[26:26];
  result[35] = (decrypt == 1'b1) ? k_r0[39:39] : k_r0[3:3];
  result[34] = (decrypt == 1'b1) ? k_r0[11:11] : k_r0[32:32];
  result[33] = (decrypt == 1'b1) ? k_r0[19:19] : k_r0[40:40];
  result[32] = (decrypt == 1'b1) ? k_r0[20:20] : k_r0[41:41];
  result[31] = (decrypt == 1'b1) ? k_r0[3:3] : k_r0[24:24];
  result[30] = (decrypt == 1'b1) ? k_r0[48:48] : k_r0[12:12];
  result[29] = (decrypt == 1'b1) ? k_r0[47:47] : k_r0[11:11];
  result[28] = (decrypt == 1'b1) ? k_r0[41:41] : k_r0[5:5];
  result[27] = (decrypt == 1'b1) ? k_r0[10:10] : k_r0[6:6];
  result[26] = (decrypt == 1'b1) ? k_r0[18:18] : k_r0[39:39];
  result[25] = (decrypt == 1'b1) ? k_r0[26:26] : k_r0[47:47];
  result[24] = (decrypt == 1'b1) ? k_r0[6:6] : k_r0[27:27];
  result[23] = (decrypt == 1'b1) ? k_r0[22:22] : k_r0[43:43];
  result[22] = (decrypt == 1'b1) ? k_r0[44:44] : k_r0[38:38];
  result[21] = (decrypt == 1'b1) ? k_r0[7:7] : k_r0[28:28];
  result[20] = (decrypt == 1'b1) ? k_r0[49:49] : k_r0[15:15];
  result[19] = (decrypt == 1'b1) ? k_r0[9:9] : k_r0[30:30];
  result[18] = (decrypt == 1'b1) ? k_r0[38:38] : k_r0[0:0];
  result[17] = (decrypt == 1'b1) ? k_r0[0:0] : k_r0[21:21];
  result[16] = (decrypt == 1'b1) ? k_r0[15:15] : k_r0[36:36];
  result[15] = (decrypt == 1'b1) ? k_r0[37:37] : k_r0[31:31];
  result[14] = (decrypt == 1'b1) ? k_r0[50:50] : k_r0[16:16];
  result[13] = (decrypt == 1'b1) ? k_r0[21:21] : k_r0[42:42];
  result[12] = (decrypt == 1'b1) ? k_r0[16:16] : k_r0[37:37];
  result[11] = (decrypt == 1'b1) ? k_r0[43:43] : k_r0[9:9];
  result[10] = (decrypt == 1'b1) ? k_r0[23:23] : k_r0[44:44];
  result[9] = (decrypt == 1'b1) ? k_r0[8:8] : k_r0[29:29];
  result[8] = (decrypt == 1'b1) ? k_r0[45:45] : k_r0[7:7];
  result[7] = (decrypt == 1'b1) ? k_r0[28:28] : k_r0[49:49];
  result[6] = (decrypt == 1'b1) ? k_r0[51:51] : k_r0[45:45];
  result[5] = (decrypt == 1'b1) ? k_r0[2:2] : k_r0[23:23];
  result[4] = (decrypt == 1'b1) ? k_r0[29:29] : k_r0[50:50];
  result[3] = (decrypt == 1'b1) ? k_r0[30:30] : k_r0[51:51];
  result[2] = (decrypt == 1'b1) ? k_r0[42:42] : k_r0[8:8];
  result[1] = (decrypt == 1'b1) ? k_r0[52:52] : k_r0[14:14];
  result[0] = (decrypt == 1'b1) ? k_r0[14:14] : k_r0[35:35];
  k2 = result;
endmethod: k2

method Bit#(48) k1(decrypt, k);
  Bit#(48) result;
  result[47] = (decrypt == 1'b1) ? k[40:40] : k[47:47];
  result[46] = (decrypt == 1'b1) ? k[4:4] : k[11:11];
  result[45] = (decrypt == 1'b1) ? k[19:19] : k[26:26];
  result[44] = (decrypt == 1'b1) ? k[53:53] : k[3:3];
  result[43] = (decrypt == 1'b1) ? k[6:6] : k[13:13];
  result[42] = (decrypt == 1'b1) ? k[34:34] : k[41:41];
  result[41] = (decrypt == 1'b1) ? k[20:20] : k[27:27];
  result[40] = (decrypt == 1'b1) ? k[24:24] : k[6:6];
  result[39] = (decrypt == 1'b1) ? k[47:47] : k[54:54];
  result[38] = (decrypt == 1'b1) ? k[41:41] : k[48:48];
  result[37] = (decrypt == 1'b1) ? k[32:32] : k[39:39];
  result[36] = (decrypt == 1'b1) ? k[12:12] : k[19:19];
  result[35] = (decrypt == 1'b1) ? k[46:46] : k[53:53];
  result[34] = (decrypt == 1'b1) ? k[18:18] : k[25:25];
  result[33] = (decrypt == 1'b1) ? k[26:26] : k[33:33];
  result[32] = (decrypt == 1'b1) ? k[27:27] : k[34:34];
  result[31] = (decrypt == 1'b1) ? k[10:10] : k[17:17];
  result[30] = (decrypt == 1'b1) ? k[55:55] : k[5:5];
  result[29] = (decrypt == 1'b1) ? k[54:54] : k[4:4];
  result[28] = (decrypt == 1'b1) ? k[48:48] : k[55:55];
  result[27] = (decrypt == 1'b1) ? k[17:17] : k[24:24];
  result[26] = (decrypt == 1'b1) ? k[25:25] : k[32:32];
  result[25] = (decrypt == 1'b1) ? k[33:33] : k[40:40];
  result[24] = (decrypt == 1'b1) ? k[13:13] : k[20:20];
  result[23] = (decrypt == 1'b1) ? k[29:29] : k[36:36];
  result[22] = (decrypt == 1'b1) ? k[51:51] : k[31:31];
  result[21] = (decrypt == 1'b1) ? k[14:14] : k[21:21];
  result[20] = (decrypt == 1'b1) ? k[1:1] : k[8:8];
  result[19] = (decrypt == 1'b1) ? k[16:16] : k[23:23];
  result[18] = (decrypt == 1'b1) ? k[45:45] : k[52:52];
  result[17] = (decrypt == 1'b1) ? k[7:7] : k[14:14];
  result[16] = (decrypt == 1'b1) ? k[22:22] : k[29:29];
  result[15] = (decrypt == 1'b1) ? k[44:44] : k[51:51];
  result[14] = (decrypt == 1'b1) ? k[2:2] : k[9:9];
  result[13] = (decrypt == 1'b1) ? k[28:28] : k[35:35];
  result[12] = (decrypt == 1'b1) ? k[23:23] : k[30:30];
  result[11] = (decrypt == 1'b1) ? k[50:50] : k[2:2];
  result[10] = (decrypt == 1'b1) ? k[30:30] : k[37:37];
  result[9] = (decrypt == 1'b1) ? k[15:15] : k[22:22];
  result[8] = (decrypt == 1'b1) ? k[52:52] : k[0:0];
  result[7] = (decrypt == 1'b1) ? k[35:35] : k[42:42];
  result[6] = (decrypt == 1'b1) ? k[31:31] : k[38:38];
  result[5] = (decrypt == 1'b1) ? k[9:9] : k[16:16];
  result[4] = (decrypt == 1'b1) ? k[36:36] : k[43:43];
  result[3] = (decrypt == 1'b1) ? k[37:37] : k[44:44];
  result[2] = (decrypt == 1'b1) ? k[49:49] : k[1:1];
  result[1] = (decrypt == 1'b1) ? k[0:0] : k[7:7];
  result[0] = (decrypt == 1'b1) ? k[21:21] : k[28:28];
  k1 = result;
endmethod: k1

endmodule




interface DESIGN_IFC_DES;
method Action  getinputs(Bit#(56) key,Bit#(64) desIn,Bit#(1) decrypt);
method Bit#(64) desOut();
endinterface: DESIGN_IFC_DES

(* 
       synthesize,
       always_ready ,
       always_enabled ,
       CLK = "clk",
       RST_N = "reset"
*)


module mkDes(DESIGN_IFC_DES);

Reg#(Bit#(64)) desIn_r();
mkRegU the_desIn_r(desIn_r);

Reg#(Bit#(56)) key_r();
mkRegU the_key_r(key_r);	

Reg#(Bit#(64)) desOutIn();
mkRegU the_desOutIn(desOutIn);

Reg#(Bit#(32)) l0();
mkRegU the_l0(l0);
Reg#(Bit#(32)) l1();
mkRegU the_l1(l1);
Reg#(Bit#(32)) l2();
mkRegU the_l2(l2);
Reg#(Bit#(32)) l3();
mkRegU the_l3(l3);
Reg#(Bit#(32)) l4();
mkRegU the_l4(l4);
Reg#(Bit#(32)) l5();
mkRegU the_l5(l5);
Reg#(Bit#(32)) l6();
mkRegU the_l6(l6);
Reg#(Bit#(32)) l7();
mkRegU the_l7(l7);
Reg#(Bit#(32)) l8();
mkRegU the_l8(l8);
Reg#(Bit#(32)) l9();
mkRegU the_l9(l9);
Reg#(Bit#(32)) l10();
mkRegU the_l10(l10);
Reg#(Bit#(32)) l11();
mkRegU the_l11(l11);
Reg#(Bit#(32)) l12();
mkRegU the_l12(l12);
Reg#(Bit#(32)) l13();
mkRegU the_l13(l13);
Reg#(Bit#(32)) l14();
mkRegU the_l14(l14);
Reg#(Bit#(32)) l15();
mkRegU the_l15(l15);

Reg#(Bit#(32)) r0();
mkRegU the_r0(r0);
Reg#(Bit#(32)) r1();
mkRegU the_r1(r1);
Reg#(Bit#(32)) r2();
mkRegU the_r2(r2);
Reg#(Bit#(32)) r3();
mkRegU the_r3(r3);
Reg#(Bit#(32)) r4();
mkRegU the_r4(r4);
Reg#(Bit#(32)) r5();
mkRegU the_r5(r5);
Reg#(Bit#(32)) r6();
mkRegU the_r6(r6);
Reg#(Bit#(32)) r7();
mkRegU the_r7(r7);
Reg#(Bit#(32)) r8();
mkRegU the_r8(r8);
Reg#(Bit#(32)) r9();
mkRegU the_r9(r9);
Reg#(Bit#(32)) r10();
mkRegU the_r10(r10);
Reg#(Bit#(32)) r11();
mkRegU the_r11(r11);
Reg#(Bit#(32)) r12();
mkRegU the_r12(r12);
Reg#(Bit#(32)) r13();
mkRegU the_r13(r13);
Reg#(Bit#(32)) r14();
mkRegU the_r14(r14);
Reg#(Bit#(32)) r15();
mkRegU the_r15(r15);

DESIGN_IFC_CRP u0();
mkCrp the_u0(u0);
DESIGN_IFC_CRP u1();
mkCrp the_u1(u1);
DESIGN_IFC_CRP u2();
mkCrp the_u2(u2);
DESIGN_IFC_CRP u3();
mkCrp the_u3(u3);
DESIGN_IFC_CRP u4();
mkCrp the_u4(u4);
DESIGN_IFC_CRP u5();
mkCrp the_u5(u5);
DESIGN_IFC_CRP u6();
mkCrp the_u6(u6);
DESIGN_IFC_CRP u7();
mkCrp the_u7(u7);
DESIGN_IFC_CRP u8();
mkCrp the_u8(u8);
DESIGN_IFC_CRP u9();
mkCrp the_u9(u9);
DESIGN_IFC_CRP u10();
mkCrp the_u10(u10);
DESIGN_IFC_CRP u11();
mkCrp the_u11(u11);
DESIGN_IFC_CRP u12();
mkCrp the_u12(u12);
DESIGN_IFC_CRP u12();
mkCrp the_u12(u12);
DESIGN_IFC_CRP u13();
mkCrp the_u13(u13);
DESIGN_IFC_CRP u14();
mkCrp the_u14(u14);
DESIGN_IFC_CRP u15();
mkCrp the_u15(u15);
DESIGN_IFC_KEY_SEL uk();
mkKey_sel the_uk(uk);

method  Action getinputs(Bit#(56) key,Bit#(64) desIn,Bit#(1) decrypt);
action
Bit#(64) ip;
Bit#(64) fp;
Bit#(32) out0, out1, out2, out3, out4, out5, out6, out7, out8;
Bit#(32)  out9, out10, out11, out12, out13, out14, out15;
Bit#(48) k1, k2, k3, k4, k5, k6, k7, k8, k9;
Bit#(48) k10, k11, k12, k13, k14, k15, k16;
// Perform the initial permutation with the registered desIn
  ip = {	desIn_r[6:6], desIn_r[14:14], desIn_r[22:22], desIn_r[30:30], desIn_r[38:38], desIn_r[46:46],
			desIn_r[54:54], desIn_r[62:62], desIn_r[4:4], desIn_r[12:12], desIn_r[20:20], desIn_r[28:28],
			desIn_r[36:36], desIn_r[44:44], desIn_r[52:52], desIn_r[60:60], desIn_r[2:2], desIn_r[10:10], 
			desIn_r[18:18], desIn_r[26:26], desIn_r[34:34], desIn_r[42:42], desIn_r[50:50], desIn_r[58:58], 
			desIn_r[0:0], desIn_r[8:8], desIn_r[16:16], desIn_r[24:24], desIn_r[32:32], desIn_r[40:40], 
			desIn_r[48:48], desIn_r[56:56], desIn_r[7:7], desIn_r[15:15], desIn_r[23:23], desIn_r[31:31], 
			desIn_r[39:39], desIn_r[47:47], desIn_r[55:55], desIn_r[63:63], desIn_r[5:5], desIn_r[13:13],
			desIn_r[21:21], desIn_r[29:29], desIn_r[37:37], desIn_r[45:45], desIn_r[53:53], desIn_r[61:61],
			desIn_r[3:3], desIn_r[11:11], desIn_r[19:19], desIn_r[27:27], desIn_r[35:35], desIn_r[43:43],
			desIn_r[51:51], desIn_r[59:59], desIn_r[1:1], desIn_r[9:9], desIn_r[17:17], desIn_r[25:25],
			desIn_r[33:33], desIn_r[41:41], desIn_r[49:49], desIn_r[57:57] };

uk.getinputs(key_r);
k1 = uk.k1(decrypt,key_r);
k2 = uk.k2(decrypt);
k3 = uk.k3(decrypt);
k4 = uk.k4(decrypt);
k5 = uk.k5(decrypt);
k6 = uk.k6(decrypt);
k7 = uk.k7(decrypt);
k8 = uk.k8(decrypt);
k9 = uk.k9(decrypt);
k10 = uk.k10(decrypt);
k11 = uk.k11(decrypt);
k12 = uk.k12(decrypt);
k13 = uk.k13(decrypt);
k14 = uk.k14(decrypt);
k15 = uk.k15(decrypt);
k16 = uk.k16(decrypt);
	
// 16 CRP blocks 
out0 =  u0.p(ip[31:0], k1 );
out1 =  u1.p(r0, k2 );
out2 =  u2.p(r1, k3 );
out3 =  u3.p(r2, k4 );
out4 =  u4.p(r3, k5 );
out5 =  u5.p(r4, k6 );
out6 =  u6.p(r5, k7 );
out7 =  u7.p(r6,k8);
out8 =  u8.p(r7,k9);
out9 =  u9.p(r8,k10);
out10 =  u10.p(r9,k11);
out11 =  u11.p(r10,k12);
out12 =  u12.p(r11,k13);
out13 =  u13.p(r12,k14);
out14 =  u14.p(r13,k15);
out15 =  u15.p(r14,k16);


// Key schedule provides a linear means of intermixing the 56 bit key to form a
//   different 48 bit key for each of the 16 bit rounds
// Register the 56 bit key
	key_r <=    key;
// Register the 64 bit getinputs
	desIn_r <=    desIn;
// 32 bit l0 get upper 32 bits of IP
        l0 <=    ip[31:0];
// 32 bit R0 gets lower 32 bits of IP XOR'd with 32 bit out0
        r0 <=     ip[63:32] ^ out0;
// 32 bit l1 gets 32 bit r0
        l1 <=    r0;
// 32 bit r1 gets 32 bit l0 XOR'd with 32 bit out1
        r1 <=    l0 ^ out1;
// 32 bit l2 gets 32 bit r1
        l2 <=    r1;
// 32 bit r2 gets 32 bit l1 XOr'd with 32 bit out2
        r2 <=    l1 ^ out2;
        l3 <=    r2;
        r3 <=    l2 ^ out3;
        l4 <=    r3;
        r4 <=    l3 ^ out4;
        l5 <=    r4;
        r5 <=    l4 ^ out5;
        l6 <=    r5;
        r6 <=    l5 ^ out6;
        l7 <=    r6;
        r7 <=    l6 ^ out7;
        l8 <=    r7;
        r8 <=    l7 ^ out8;
        l9 <=    r8;
        r9 <=    l8 ^ out9;
        l10 <=    r9;
        r10 <=    l9 ^ out10;
        l11 <=    r10;
        r11 <=    l10 ^ out11;
        l12 <=    r11;
        r12 <=    l11 ^ out12;
        l13 <=    r12;
        r13 <=    l12 ^ out13;
        l14 <=    r13;
        r14 <=    l13 ^ out14;

// 32 bit l15 gets 32 bit r14
        l15 <=    r14;
// 32 bit r15 gets 32 bit l14 XOr'd with 32 bit out15
        r15 <=    l14 ^ out15;



// XOr 32 bit out15 with 32 bit l14         ( fp  1:32 )
//    then concatinate the 32 bit r14 value ( fp 33:64 )
//       This value ( fp 1:64 ) is then registered by the desOut[63:0] register 
 fp = { (out15 ^ l14), r14};
// Perform the final permutation
	desOutIn <=    {	fp[24:24], fp[56:56], fp[16:16], fp[48:48], fp[8:8], fp[40:40], fp[0:0], fp[32:32], 
			fp[25:25], fp[57:57], fp[17:17], fp[49:49], fp[9:9], fp[41:41], fp[1:1], fp[33:33], 
			fp[26:26], fp[58:58], fp[18:18], fp[50:50], fp[10:10], fp[42:42], fp[2:2], fp[34:34], 
			fp[27:27], fp[59:59], fp[19:19], fp[51:51], fp[11:11], fp[43:43], fp[3:3], fp[35:35], 
			fp[28:28], fp[60:60], fp[20:20], fp[52:52], fp[12:12], fp[44:44], fp[4:4], fp[36:36], 
			fp[29:29], fp[61:61], fp[21:21], fp[53:53], fp[13:13], fp[45:45], fp[5:5], fp[37:37],
			fp[30:30], fp[62:62], fp[22:22], fp[54:54], fp[14:14], fp[46:46], fp[6:6], fp[38:38], 
			fp[31:31], fp[63:63], fp[23:23], fp[55:55], fp[15:15], fp[47:47], fp[7:7], fp[39:39] };

endaction
endmethod: getinputs

method Bit#(64) desOut();
 desOut = desOutIn;
endmethod: desOut

endmodule
