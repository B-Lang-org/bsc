import FIFO::*;
import RegFile::*;

typedef Bit#(32) Data;
typedef Bit#(33) Datapath;	// DataIn+1 : one for carry-out

typedef struct {
	Bit#(op_size) opcode;	
	Bit#(res_size)	reserved;
	Bit#(ctl_size)	sel;
} Unit_Ctl#(type op_size, type res_size, type ctl_size) 
	deriving (Bits, Eq);

typedef Unit_Ctl #(4,2,2) UnitCtl;

typedef enum {
        Choose_i1,
        Choose_i2,
        Choose_result,
        Choose_const
} OutCtl deriving (Bits, Eq);

// common interface for all units except LSU and Set
interface BinFU;
	method Bool chk_exception();
	method Data result();
	method Action write_inp(Data i1, Data i2, UnitCtl ctl);
endinterface

typedef struct {
	Unit_Ctl#(op_size,reserved_size,ctl_size) addrgen;	// 
	Unit_Ctl#(op_size,reserved_size,ctl_size) lsu;	// Load store unit
	Unit_Ctl#(op_size,reserved_size,ctl_size) shf1;	// 
	Unit_Ctl#(op_size,reserved_size,ctl_size) mul;	// Multiplier unit
	Unit_Ctl#(op_size,reserved_size,ctl_size) set1;	// 
	Unit_Ctl#(op_size,reserved_size,ctl_size) add1;	// 
	Unit_Ctl#(op_size,reserved_size,ctl_size) add2;	// 
	Unit_Ctl#(op_size,reserved_size,ctl_size) add3;	// 
	Unit_Ctl#(op_size,reserved_size,ctl_size) add4;	// 
	Unit_Ctl#(op_size,reserved_size,ctl_size) set2;	// 
	Unit_Ctl#(op_size,reserved_size,ctl_size) shf2;	// 
	Unit_Ctl#(op_size,reserved_size,ctl_size) shf3;	// 
	Unit_Ctl#(op_size,reserved_size,ctl_size) shf4;	// 
	Unit_Ctl#(op_size,reserved_size,ctl_size) shf5;	// Shifter
} Config_Word#(type op_size, type reserved_size, type ctl_size) 
	deriving (Bits, Eq);

typedef struct {
	Data 	lsu_din;
	Data 	adr_i1;
	Data 	adr_i2;
	Data 	shf_i1;
	Data 	shf_i2;
	Data 	mul_i1;
	Data 	mul_i2;
	Data 	set_i1;
	Data 	set_i2;
} DataInp deriving(Bits, Eq);

typedef struct {
	Data 	shf2_o;
	Data 	shf3_o;
	Data 	shf4_o;
	Data 	shf5_o;
	Data 	set2_o;
} DataOut deriving(Bits, Eq);

module mkTester #(String testfile) 
   ( Empty );

   RegFile#(Bit#(3), Tuple3#(DataInp , Config_Word#(4,2,2) , DataOut ) )  test_ifc();
   mkRegFileFullLoad#(testfile) iarray(test_ifc) ;
   
   // An index to the array
   Reg#(Bit#(3) )  counter() ;
   mkReg#(0) icounter(counter) ;


   rule test ;
      action
         let {d, c, o} = test_ifc.sub(counter) ;
	$display("Read %h for d",d);
	$display("Read %h for c",c);
	$display("Read %h for o",o);
        counter <= counter + 1 ;
      endaction
   endrule


   rule finish_sim (counter == ( 3'b111 )) ;
      action
         $finish(0);
      endaction
   endrule
   
endmodule

module sysWideRF(Empty) ;

   Empty tester <- mkTester("mem.dat");

endmodule


