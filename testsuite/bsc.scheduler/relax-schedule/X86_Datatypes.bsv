package X86_Datatypes;

/*********** Basic Datatypes ***********/

typedef Bit#(5)   RegAddress;
typedef Int#(16)  SImmediate;
typedef UInt#(16) UImmediate;
typedef Int#(16)  SignExtend;
typedef Int#(14)  SignExtend14;
typedef Int#(24)  LImmediate;
typedef Bit#(5)   CondAddress;
typedef Int#(14)  Displacement;
typedef Bit#(3)   CondField;
typedef Bit#(10)  TimeBase;
typedef Bit#(8)   FPMask;
typedef Bit#(4)   Immediate;
typedef Bit#(10)  SPRegAddress;
typedef Bit#(4)   SegmentAddress; 
typedef Bit#(5)   Mask;
typedef Bit#(6)   MaskX;
typedef Bit#(5)   NumBytes;
typedef Bit#(5)   TrapConditions;
typedef Bit#(5)   Shift;
typedef Bit#(6)   ShiftX;

typedef Bit#(8)   CondMask;
typedef Bit#(4)   CondRegMask;
typedef Bit#(5)   BranchOptions;


/*********** Decoded Instruction **************/

/***************** FXU types ******************/

// todo, no further granularity about the actual operations right now
typedef enum
{
  FXU_arith,
  FXU_shift,
  FXU_logic,
  FXU_mult,
  FXU_divd
} FXU_Op deriving (Bits, Eq);

// todo, no further granularity about the actual operations right now
typedef enum
{
  FPU_arith,
  FPU_mult,
  FPU_divd,
  FPU_sine
} FPU_Op deriving (Bits, Eq);

/***************** FUU types ******************/
/*                                            */
/**********************************************/

typedef union tagged 
{
  ArithOptions 		FUU_arith;
  LogicOptions  	FUU_logic;
  CompareOptions	FUU_compare;
  CountLZOptions	FUU_count_lz;
  CondRegOp 	      	FUU_cond;
  DivOptions		FUU_divide;
  ExtendOptions 	FUU_extend_sign;
  FloatingOp  	      	FUU_floating;
  MoveOptions 	      	FUU_move;
  MulOptions		FUU_multiply;
  RotateOptions 	FUU_rotate_left;
  ShiftLeftOptions	FUU_shift_left;
  ShiftRightOptions	FUU_shift_right;
} 
  FUU_Op deriving(Eq,Bits);

/*************** Arith Subtypes ***************/
/*                                            */
/* Groups covered: add, neg, sub              */
/* Estimated Bits: 30                         */
/*                                            */
/**********************************************/

typedef enum 
{
  AAdd,
  ANeg,
  ASubf
}
 ArithOp deriving (Bits,Eq);

typedef struct 
{
  ArithOp op;
  Bool swapargs;
  Bool carrying;
  Bool extended;
  Bool record;
  Bool shifted;
  Bool oe;
  Bool rc;
}
 ArithOptions deriving (Eq,Bits);

/*************** Logic Subtypes *****************/
/*                                              */
/* Groups covered: and, or, nand, nor, xor, eqv */
/* Estimated Bits: 14                           */
/*                                              */
/************************************************/

typedef enum 
{
  LOG_and,
  LOG_or,
  LOG_xor,
  LOG_nand,
  LOG_nor,
  LOG_eqv
}
 LogicOp deriving (Bits,Eq);

typedef struct 
{
  LogicOp op;
  Bool complement;
  Bool shifted;
  Bool rc;
}
 LogicOptions deriving (Eq,Bits);

/************** Compare Subtypes ****************/
/*                                              */
/* Groups covered: cmp, cmpl                    */
/* Estimated Bits: 21                           */
/*                                              */
/************************************************/

typedef struct
{
  Bool logical;
  Bool sixtyfour;
}
  CompareOptions deriving (Eq,Bits); 

/************** CondReg Subtypes ****************/
/*                                              */
/* Groups covered: crand, cror, etc. (cr)       */
/* Estimated Bits: 19                           */
/*                                              */
/************************************************/

typedef enum
{
  CR_and,
  CR_andc,
  CR_eqv,
  CR_nand,
  CR_nor,
  CR_or,
  CR_orc,
  CR_xor
}
  CondRegOp deriving (Bits,Eq);


/************** CountLeadingZeroes **************/
/*                                              */
/* Groups covered: cntlz                        */
/* Estimated Bits: 11                           */
/*                                              */
/************************************************/

typedef struct
{
  Bool doubleword;
  Bool rc;
}
  CountLZOptions deriving (Eq,Bits);



/**************** Divide Subgroup ***************/
/*                                              */
/* Groups covered: div                          */
/* Estimated Bits: 19                           */
/*                                              */
/************************************************/

typedef struct 
{
  Bool doubleword;
  Bool unsign;
  Bool oe;
  Bool rc;
}
  DivOptions deriving (Eq,Bits);

/****************** ExtendSign ******************/
/*                                              */
/* Groups covered: exts                         */
/* Estimated Bits: 12                           */
/*                                              */
/************************************************/

typedef enum 
{
  EByte,
  EHalfword,
  EWord
}
  ExtendType deriving (Eq,Bits);

typedef struct 
{
  ExtendType ext;
  Bool rc;
}
  ExtendOptions deriving (Eq,Bits);
  
/***************** FloatingPoint ****************/
/*                                              */
/* Groups covered: f                            */
/* Estimated Bits: 28                           */
/*                                              */
/************************************************/
  
typedef struct 
{
  Bool sixtyfour;
  Bool ordered;
}
  FCondOptions deriving (Eq,Bits);

typedef struct 
{
  Bool doubleword;
  Bool round;
  Bool ordered;
}
  FConvOptions deriving (Eq,Bits);
  
typedef union tagged 
{
  void F_abs;
  Bool F_add;	//Single (fadds) if true
  Bool F_cfid;
  FCondOptions F_cmp;
  FConvOptions F_ctdi;
  Bool F_div;	//Single (fdivs) if true
  Bool F_madd;
  void F_mr;
  void F_nabs;
  void F_neg;
  void F_res;
  void F_rsp;
  void F_rsqrte;
  Bool F_msub;
  Bool F_mul;
  Bool F_nmadd;
  Bool F_nmsub;
  void F_sel;
  Bool F_sqrt;
  Bool F_sub;
}
  FloatingOp deriving (Eq,Bits);


/******************* Multiply *******************/
/*                                              */
/* Groups covered: mul                          */
/* Estimated Bits: 15                           */
/*                                              */
/************************************************/

typedef struct 
{
  Bool doubleword;
  Bool unsign;
  Bool high;
  Bool oe;
  Bool rc;
}
  MulOptions deriving (Eq,Bits);

/******************* Rotate *********************/
/*                                              */
/* Groups covered: rl                           */
/* Estimated Bits: 31                           */
/*                                              */
/************************************************/

typedef struct 
{
  MaskX       mb; // These should be six bit for alignment. 
  MaskX       me;
  Bool        rc;
  Bool        partialReplace; // Set when the operation may not completely overwrite old value
  Bool        doubleword;
}
  RotateOptions deriving (Eq,Bits);

/***************** ShiftLeft ********************/
/*                                              */
/* Groups covered: sl                           */
/* Estimated Bits: 17                           */
/*                                              */
/************************************************/

typedef struct 
{
  Bool doubleword;
  Bool rc;
}
  ShiftLeftOptions deriving (Eq,Bits);
  
/***************** ShiftRight *******************/
/*                                              */
/* Groups covered: sr                           */
/* Estimated Bits: 20                           */
/*                                              */
/************************************************/

typedef struct 
{
  Bool algebraic;
  Bool doubleword;
  Bool rc;
}
  ShiftRightOptions deriving (Eq,Bits);

/******************** Moves *********************/
/*                                              */
/* Groups covered: mc, mf, mt                   */
/* Estimated Bits: 5 + ??                       */
/*                                              */
/************************************************/

//NOTE: The move group is the least general of
//      the decoded instruction groups.

typedef union tagged 
{
  void M_crf;
  void M_crfs;
  void M_crxr;
  void M_fcr;
  void M_ffs;
  void M_fmsr;
  void M_fspr;
  void M_fsr;
  void M_fsrin;
  void M_ftb;	
  void M_tcrf;
  void M_tfsb0;
  void M_tfsb1;
  void M_tfsf;
  void M_tfsfi;
  void M_tmsr;
  void M_tspr;
  void M_tsr;
  void M_tsrin;
}
  MoveOptions deriving (Eq,Bits);
  

/******************* Load/Store *****************/
/*                                              */
/* Groups covered: l, s                         */
/* Estimated Bits: 30                           */
/*                                              */
/************************************************/
  
typedef Either#(RegAddress, SignExtend) LSSource;

typedef enum
{
  LSLoad,
  LSStore
} 
  LSOp deriving(Eq,Bits);

typedef enum 
{
  LS_byte,
  LS_doubleword,
  LS_floating_double,
  LS_floating_single,
  LS_halfword,
  LS_multiple_word,
  LS_string_word,
  LS_word
}
  LSType deriving (Eq,Bits);
  
typedef struct 
{
  LSType lstype;
  LSOp op; 
  Bool reserved_conditional; // for lwarx and swcx. and friends
  Bool byte_reverse;
  Bool algebraic;     // zero otherwise
  Bool update;
  Bool indexed;
}
  LSU_Op deriving (Eq,Bits);
  
/****************** TRAP GROUP ******************/
/*                                              */
/* The group of traps, system calls, and CCU    */
/* handled operations such as sync.             */
/* Estimated Bits: 13                           */
/*                                              */
/************************************************/

typedef enum
{
  TRAP_isync,
  TRAP_rfi,
  TRAP_sc,
  TRAP_sync,
  TRAP_td,
  TRAP_tw
}
  TRAP_Op deriving (Eq, Bits);

/******************** Trap **********************/
/*                                              */
/* Groups covered: td, tw                       */
/* Estimated Bits: 22                           */
/*                                              */
/************************************************/

typedef enum
{
  BR_branch,
  BR_branch_conditional,
  BR_bc_link,
  BR_bc_counter
} 
  BranchType deriving(Eq,Bits);

typedef struct
{
   BranchType btype;
   BranchOptions options;
   Bool absAddress;
   Bool linkBit;
} 
  BRU_Op deriving (Eq,Bits);


/****************** DIO GROUP *******************/
/*                                              */
/* The group that talks to the data cache.      */
/* Estimated Bits: 13                           */
/*                                              */
/************************************************/

typedef enum
{
  DIO_dcbf,
  DIO_dcbi,
  DIO_dcbst,
  DIO_dcbt,
  DIO_dcbtst,
  DIO_dcbz,
  DIO_eciwx,
  DIO_ecowx,
  DIO_eieio,
  DIO_slbia,
  DIO_slbie,
  DIO_tlbia,
  DIO_tlbie,
  DIO_tlbsync
}
  DIO_Op deriving (Eq, Bits);
  
/**************** DataCacheBlock ****************/
/*                                              */
/* Groups covered: dcb                          */
/* Estimated Bits: 13                           */
/*                                              */
/************************************************/

  
/********** Decoded Instruction Type ************/
/*                                              */
/* The main decoded instruction type.           */
/* Unimplemented instructions will be handled   */
/* by the OS.                                   */
/*                                              */
/* Estimated Bits: 38                           */
/*                                              */
/************************************************/

// for the timing model, no need to differentiate Immediate value
typedef union tagged
{ 
  RegAddress    SRC_Reg;
  CondAddress   SRC_Cond;
  Bit#(24)      SRC_Immediate;
}
  SecondSource deriving(Eq, Bits);  

typedef struct 
{
  DecodedData                         data;
  Bool                                last_uop;
  Either#(RegAddress, CondAddress)    dest;
  Either#(RegAddress, CondAddress)    source1;
  SecondSource                        source2;
  Either#(RegAddress, CondAddress)    source3;
}
  DecodedInstruction deriving(Eq,Bits);

//For stores: source1: address, source2: offset, source3: data

typedef union tagged
{
  FUU_Op     DEC_FUU;
  FXU_Op     DEC_FXU;
  FPU_Op     DEC_FPU;
  LSU_Op     DEC_LSU;
  BRU_Op     DEC_BRU;
  DIO_Op     DEC_DIO;
  TRAP_Op    DEC_TRAP;
  Bit#(32)   DEC_UNIMPLEMENTED;
  void       DEC_UNDEFINED;
}
  DecodedData deriving (Eq, Bits);

/*********** Branch ***********/

typedef struct
{
  LImmediate immediate;
  Bool absAddress;
  Bool linkBit;
} BranchData deriving (Eq,Bits);
//USED BY: b

typedef struct
{
  BranchOptions options;
  CondAddress condition;
  Displacement branchDisp;
  Bool absAddress;
  Bool linkBit;
} BranchOptionAddressed deriving (Eq,Bits);
//USED BY: bc

typedef struct
{
  BranchOptions options;
  CondAddress condition;
  Bool linkBit;
} BranchOptionField deriving (Eq,Bits);
//USED BY: bcctr, bclr

/*************** Helper Functions ************************/

function CondRegMask getCondMask(Bit#(2) m);
  return case (m) //gives the IBM ordering
      2'b00:
        return 4'b0001;
      2'b01:
        return 4'b0010;
      2'b10:
        return 4'b0100;
      2'b11:
        return 4'b1000;
      endcase;
endfunction

/************* Skeleton for Decoded Instruction **************/

function Tuple2#(Maybe#(RegAddress), Maybe#(Tuple2#(CondField, CondRegMask)))
  getDest(DecodedInstruction inst);
  
  function normalDest(i, rc);
    return case (i.dest) matches    
      tagged Left .r:
	return rc? 
	  tuple2(Just(r), Just(tuple2(3'b000, 4'b1111)))
	  : tuple2(Just(r), Nothing);
      tagged Right .c:
	return tuple2(Nothing, Just(tuple2(c[4:2], 4'b1111)));
      endcase;
  endfunction
  
  return case (inst.data) matches
    tagged DEC_FUU .fop:
      return case (fop) matches
        tagged FUU_arith .fdata:
	  return normalDest(inst, fdata.rc);
        tagged FUU_logic .fdata:
	  return normalDest(inst, fdata.rc);
	tagged FUU_compare .fdata:
	  return normalDest(inst, True);
	tagged FUU_count_lz .fdata:
	  return normalDest(inst, fdata.rc);
	tagged FUU_cond .fdata:
	  return case (inst.dest) matches
	    tagged Left .r:
	      return tuple2(Nothing, Nothing);
	    tagged Right .c:
	      return tuple2(Nothing, Just(tuple2(c[4:2], getCondMask(c[1:0]))));
	    endcase;
	tagged FUU_divide .fdata:
	  return normalDest(inst, fdata.rc);
	tagged FUU_extend_sign .fdata:
	  return normalDest(inst, fdata.rc);
	tagged FUU_floating .fdata:
	  return normalDest(inst, False);
	tagged FUU_move .fdata:
	  return normalDest(inst, False);
	tagged FUU_multiply .fdata:
	  return normalDest(inst, fdata.rc);
	tagged FUU_rotate_left .fdata:
	  return normalDest(inst, fdata.rc);
	tagged FUU_shift_right .fdata:
	  return normalDest(inst, fdata.rc);
      endcase;
    tagged DEC_LSU .lop:
      return case (lop.op) matches
        tagged LSLoad:
	  return normalDest(inst, lop.reserved_conditional);
	tagged LSStore:
	  return tuple2(Nothing, Nothing);
	endcase;
    tagged DEC_BRU .bop:
      return tuple2(Nothing, Nothing);
    tagged DEC_DIO .dop:
      return tuple2(Nothing, Nothing);
    tagged DEC_TRAP .top:
      return tuple2(Nothing, Nothing);
  endcase;
endfunction


function Maybe#(RegAddress)
  getDest2(DecodedInstruction inst);
  
  return case (inst.data) matches
    tagged DEC_LSU .lop:
      return lop.update? case (inst.source1) matches
        tagged Left .r:
	  return Just(r);
	tagged Right .i:
	  return Nothing;
	endcase
      : Nothing;
    default
      return Nothing;
    endcase;
endfunction

function Tuple3#(Maybe#(RegAddress), Maybe#(Tuple2#(CondField, CondRegMask)), Maybe#(Bit#(64)))
  getSrc1(DecodedInstruction inst);
   
  function normalSrc1(i);
    return case (i.source1) matches
      tagged Left .r:
        return tuple3(Just(r), Nothing, Nothing);
      tagged Right .c:
        return tuple3(Nothing, Just(tuple2(c[4:2], getCondMask(c[1:0]))), Nothing);
      endcase;
  endfunction
  
  function swapSrc1(i,swap); //This fixes up things for subfze, etc.
    if (swap)
      return case (i.source2) matches
        tagged SRC_Reg .r:
	  return tuple3(Just(r), Nothing, Nothing);
        tagged SRC_Cond .c:
	  return tuple3(Nothing, Just(tuple2(c[4:2], getCondMask(c[1:0]))), Nothing);
	tagged SRC_Immediate .i:
	  return tuple3(Nothing, Nothing, Just(signExtend(i)));
	endcase;
    else
      return case (i.source1) matches
	tagged Left .r:
          return tuple3(Just(r), Nothing, Nothing);
	tagged Right .c:
          return tuple3(Nothing, Just(tuple2(c[4:2], getCondMask(c[1:0]))), Nothing);
	endcase;
  endfunction
  
  return case (inst.data) matches
    tagged DEC_FUU .fop:
      return case (fop) matches
        tagged FUU_arith .fdata:
	  return swapSrc1(inst, fdata.swapargs);
	tagged FUU_move .fdata: //XXX Support moves here
	  return tuple3(Nothing, Nothing, Nothing);
	default:
	  return normalSrc1(inst);
      endcase;
    tagged DEC_LSU .lop: //This handles the fact that LS insts use R0 as literal zero.
      return case (inst.source1) matches
	tagged Left .r:
          return r == 5'd0? tuple3(Nothing, Nothing, Just(64'd0)): tuple3(Just(r), Nothing, Nothing);
	tagged Right .c:
          return tuple3(Nothing, Just(tuple2(c[4:2], getCondMask(c[1:0]))), Nothing);
	endcase;
    tagged DEC_BRU .bop:
      return case (bop.btype)
        BR_branch:
	  return tuple3(Nothing, Nothing, Nothing);
	BR_branch_conditional:	
	  return case (inst.source1) matches
	    tagged Left .r:
	      return ?;
	    tagged Right .c:
	      return tuple3(Nothing, Just(tuple2(c[4:2], getCondMask(c[1:0]))), Nothing);
	    endcase;
	BR_bc_link:
	  return case (inst.source1) matches
	    tagged Left .r:
	      return ?;
	    tagged Right .c:
	      return tuple3(Nothing, Just(tuple2(c[4:2], getCondMask(c[1:0]))), Nothing);
	    endcase;
	BR_bc_counter:
	  return case (inst.source1) matches
	    tagged Left .r:
	      return ?;
	    tagged Right .c:
	      return tuple3(Nothing, Just(tuple2(c[4:2], getCondMask(c[1:0]))), Nothing);
	    endcase;
      endcase;
    tagged DEC_DIO .dop:
      return case (dop)
	DIO_slbia,
	DIO_slbie,
	DIO_tlbia,
	DIO_tlbie,
	DIO_tlbsync,
	DIO_eieio:
	  return tuple3(Nothing, Nothing, Nothing);
	default:
	  return normalSrc1(inst);
      endcase;
    tagged DEC_TRAP .top:
      return case (top)
	TRAP_td,
	TRAP_tw:
	  return normalSrc1(inst);
	default:
	  return tuple3(Nothing, Nothing, Nothing);
      endcase;
  endcase;
endfunction

function Tuple3#(Maybe#(RegAddress), Maybe#(Tuple2#(CondField, CondRegMask)), Maybe#(Bit#(64)))
  getSrc2(DecodedInstruction inst);
   
  function normalSrc2(in, se); //Bool is signExtend vs zeroExtend
    return case (in.source2) matches
      tagged SRC_Reg .r:
        return tuple3(Just(r), Nothing, Nothing);
      tagged SRC_Cond .c:
        return tuple3(Nothing, Just(tuple2(c[4:2], getCondMask(c[1:0]))), Nothing);
      tagged SRC_Immediate .i:
        return se?
	  tuple3(Nothing, Nothing, Just(signExtend(i)))
	  : tuple3(Nothing, Nothing, Just(zeroExtend(i)));
      endcase;
  endfunction
   
  function swapSrc2(i,swap); //This fixes up things for subfze, etc.
    if (swap)
      return case (i.source1) matches
	tagged Left .r:
          return tuple3(Just(r), Nothing, Nothing);
	tagged Right .c:
          return tuple3(Nothing, Just(tuple2(c[4:2], getCondMask(c[1:0]))), Nothing);
	endcase;
    else
      return case (i.source2) matches
        tagged SRC_Reg .r:
	  return tuple3(Just(r), Nothing, Nothing);
        tagged SRC_Cond .c:
	  return tuple3(Nothing, Just(tuple2(c[4:2], getCondMask(c[1:0]))), Nothing);
	tagged SRC_Immediate .i:
	  return tuple3(Nothing, Nothing, Just(signExtend(i)));
	endcase;
  endfunction
  
  return case (inst.data) matches
    tagged DEC_FUU .fop:
      return case (fop) matches
        tagged FUU_arith .fdata:
	  return swapSrc2(inst, fdata.swapargs);
        tagged FUU_logic .fdata:
	  return normalSrc2(inst, False);
	tagged FUU_move .fdata: //XXX Support conditional moves here
	  return tuple3(Nothing, Nothing, Nothing);
        tagged FUU_compare .fdata:
	  return normalSrc2(inst, !fdata.logical);
	default:
	  return normalSrc2(inst, True);
      endcase;
    tagged DEC_LSU .lop:
      return normalSrc2(inst, True);
    tagged DEC_BRU .bop:
      return case (bop.btype)
        BR_branch:	
	  return case (inst.source2) matches
	    tagged SRC_Immediate .i:
	      return tuple3(Nothing, Nothing, Just(signExtend(i)));
	    default:
	      return ?;
	    endcase;
	BR_branch_conditional:		
	  return case (inst.source2) matches
	    tagged SRC_Immediate .i:
	      return tuple3(Nothing, Nothing, Just(signExtend(i)));
	    default:
	      return ?;
	    endcase;
	default:
	  return tuple3(Nothing, Nothing, Nothing);
      endcase;
    tagged DEC_DIO .dop:
      return case (dop)
	DIO_slbia,
	DIO_slbie,
	DIO_tlbia,
	DIO_tlbie,
	DIO_tlbsync,
	DIO_eieio:
	  return tuple3(Nothing, Nothing, Nothing);
	default:
	  return normalSrc2(inst, True);
      endcase;
    tagged DEC_TRAP .top:
      return case (top)
	TRAP_td,
	TRAP_tw:
	  return normalSrc2(inst, True);
	default:
	  return tuple3(Nothing, Nothing, Nothing);
      endcase;
  endcase;
endfunction

function Tuple3#(Maybe#(RegAddress), Maybe#(Tuple2#(CondField, CondRegMask)), Maybe#(Bit#(64)))
  getSrc3(DecodedInstruction inst);
  
  function normalSrc3(i);
    return case (i.source3) matches
      tagged Left .r:
        return tuple3(Just(r), Nothing, Nothing);
      tagged Right .c:
        return tuple3(Nothing, Just(tuple2(c[4:2], getCondMask(c[1:0]))), Nothing);
      endcase;
  endfunction
  
  return case (inst.data) matches
    tagged DEC_FUU .fop:
      return case (fop) matches
        tagged FUU_rotate_left .rop:
	  return rop.partialReplace? normalSrc3(inst) : tuple3(Nothing, Nothing, Nothing);
        default:
	  return tuple3(Nothing, Nothing, Nothing);
      endcase;
    tagged DEC_LSU .lop:
      return case (lop.op) matches
        tagged LSLoad:
	  return tuple3(Nothing, Nothing, Nothing);
	tagged LSStore:
	  return normalSrc3(inst);
      endcase;
    endcase;
  
endfunction

function Bool readsCTR(DecodedInstruction inst);
  return case (inst.data) matches //XXX Also mfspr if spr9
    tagged DEC_BRU .bop:
      return case (bop.btype) 	
        BR_bc_counter:
	  return True;
	default:
	  return False;
	endcase;
    default:
      return False;
    endcase;
endfunction


function Bool readsLNK(DecodedInstruction inst);
  return case (inst.data) matches //XXX Also mtspr/mfspr if spr8
    tagged DEC_BRU .bop:
      return case (bop.btype) 	
        BR_bc_link:
	  return True;
	default:
	  return False;
	endcase;
    default:
      return False;
    endcase;
endfunction

function Bool readsXER(DecodedInstruction inst);
  
  return case (inst.data) matches //XXX Also mtspr/mfspr and mcrxr
    tagged DEC_FUU .fop:
      return case (fop) matches
        tagged FUU_arith .fdata:
	  return fdata.extended;
	endcase;
    endcase;
endfunction

function Bool writesCTR(DecodedInstruction inst);
  return case (inst.data) matches //XXX Also mtspr if spr9
    tagged DEC_BRU .bop:
      return case (bop.btype) matches
        BR_branch_conditional:
	  return bop.options[2] == 0; //Decrements CTR and tests it.
	default:
	  return False;
	endcase;
    default:
      return False;
    endcase;
endfunction


function Bool writesLNK(DecodedInstruction inst);
  return case (inst.data) matches //XXX Also mtspr/mfspr if spr8
    tagged DEC_BRU .bop:
      return bop.linkBit;
    default:
      return False;
    endcase;
endfunction

function Bool writesXER(DecodedInstruction inst);
  
  return case (inst.data) matches //XXX Also mtspr/mfspr and mcrxr
    tagged DEC_FUU .fop:
      return case (fop) matches
        tagged FUU_arith .fdata:
	  return fdata.extended || fdata.carrying;
	tagged FUU_shift_right .fdata:
	  return fdata.algebraic;
	endcase;
    default:
      return False;
    endcase;
endfunction

function DecodedData getOp(DecodedInstruction x);
  return (x.data);
endfunction



function Bool isStore(DecodedInstruction inst);
  
  return case (inst.data) matches //XXX Also mtspr/mfspr and mcrxr
    tagged DEC_LSU .lop:
      return case (lop.op) matches
        tagged LSStore:
	  return True;
	tagged LSLoad:
	  return False;
	endcase;
      default:
        return False;
    endcase;
endfunction







function Bool isJump(Bit#(32) ins);
  return case (ins[31:26])
    6'b010000,
    6'b010010:
      return True;
    6'b010011: 
      return case (ins[10:1])
	10'b0000010000,
	10'b1000010000: 
          return True;
	default: 
          return False;
      endcase;
    default:
      return False;
  endcase;
endfunction

endpackage
