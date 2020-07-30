package Input;

typedef struct {Bit#(128) a;
                Bit#(6) ex_crs_1_1;
                Bit#(6) ex_crs_1_2;
                Bit#(6) ex_crs_1_3;
                Bit#(36) ex_crs_2_1;
                Bit#(36) ex_crs_2_2;
                Bit#(66) ex_crs_3;
                Bit#(6) ex_tch_1_1;
                Bit#(6) ex_tch_1_2;
                Bit#(6) ex_tch_1_3;
                Bit#(6) ex_tch_1_4;
                Bit#(6) ex_tch_1_5;
                Bit#(6) ex_tch_1_6;
                Bit#(32) ex_tch_2_1;
                Bit#(32) ex_tch_2_2;
                Bit#(32) ex_tch_2_3;
                Bit#(64) ex_tch_2_4;
                Bit#(64) ex_tch_2_5;
                Bit#(96) ex_tch_2_6;
                Bit#(36) con_crs_1;
                Bit#(68) con_crs_2;
                Bit#(100) con_crs_3;
                Bit#(32) con_tch_1_1;
                Bit#(64) con_tch_1_2;
                Bit#(96) con_tch_1_3;
                Bit#(128) con_tch_1_4;
				} Inputs deriving(Bits,Eq);

endpackage : Input 
