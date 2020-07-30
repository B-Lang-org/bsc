package PPC_Datatypes;

/*********** Basic Datatypes ***********/

//typedef Bit#(5)   RegAddress;
typedef Int#(16)  SImmediate;
typedef UInt#(16) UImmediate;
typedef Int#(16)  SignExtend;
typedef Int#(14)  SignExtend14;
typedef Int#(24)  LImmediate;
typedef Int#(14)  Displacement;
typedef Bit#(3)   CondField;
typedef Bit#(4)   CondValue;
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
typedef Bit#(32)  PPC_Instruction;
typedef Bit#(5)   Epoch;
typedef Bit#(5)   BranchOptions;



/********* RegAddress ***********************/


typedef union tagged
{
  void SPR_XER;
  void SPR_LR;
  void SPR_CTR;
  void SPR_DSISR;
  void SPR_DAR;
  void SPR_DEC;
  void SPR_SDR1;
  void SPR_MSR;
  void SPR_SRR0;
  void SPR_SRR1;
  void SPR_SPRG0;
  void SPR_SPRG1;
  void SPR_SPRG2;
  void SPR_SPRG3;
  void SPR_ASR;
  void SPR_EAR;
  void SPR_PVR;
  void SPR_TBL;
  void SPR_TBU;
  void SPR_IBAT0U;
  void SPR_IBAT0L;
  void SPR_IBAT1U;
  void SPR_IBAT1L;
  void SPR_IBAT2U;
  void SPR_IBAT2L;
  void SPR_IBAT3U;
  void SPR_IBAT3L;
  void SPR_DBAT0U;
  void SPR_DBAT0L;
  void SPR_DBAT1U;
  void SPR_DBAT1L;
  void SPR_DBAT2U;
  void SPR_DBAT2L;
  void SPR_DBAT3U;
  void SPR_DBAT3L;  
} 
  SPR_Name deriving(Eq,Bits);

typedef union tagged{
  Bit#(5)   Reg_Normal;
  SPR_Name  Reg_SPR;
  Bit#(4)   Reg_SR; //Segment Register
} RegAddress deriving(Eq,Bits);

typedef union tagged
{
  Bit#(5) FReg_Normal; //FPR
  CRegAddress FReg_FPSCR; //Floating Point Status field
}
  FPRAddress deriving(Eq, Bits);
  
instance Ord#(RegAddress);
  function \> (RegAddress a, RegAddress b);
    return(toDynamicIndex(a) > toDynamicIndex(b));
  endfunction
  function \>= (RegAddress a, RegAddress b);
    return(toDynamicIndex(a) >= toDynamicIndex(b));
  endfunction
  function \< (RegAddress a, RegAddress b);
    return(toDynamicIndex(a) < toDynamicIndex(b));
  endfunction
  function \<= (RegAddress a, RegAddress b);
    return(toDynamicIndex(a) <= toDynamicIndex(b));
  endfunction
endinstance
  
instance Literal#(RegAddress);
  function RegAddress fromInteger (Integer x);
    if ((x >=0) && (x < 32)) // first 32
      begin
        Bit#(5) t = fromInteger(x);
        return (tagged Reg_Normal (t));
      end
    else if ((x >= 32) && (x< 67)) // 35 SPRs
      begin
        SPR_Name pval = unpack(fromInteger(x-32));
        return (tagged Reg_SPR(pval));
      end
    else if ((x >= 67) &&  (x < 83))
      begin
        Bit#(4) t = fromInteger(x-67);
        return (tagged Reg_SR (t));
      end
    else
      return (?);
  endfunction
  function Bool inLiteralRange(RegAddress a, Integer i);
     return(i >= 0 && i < 83);
   endfunction
endinstance

instance PrimIndex#(RegAddress,7);
  // simulate a default method-style implementation
  function Bool isStaticIndex(RegAddress a);
     return(isStaticIndex(toDynamicIndex(a)));
  endfunction
  function Integer toStaticIndex(RegAddress a);
     return(toStaticIndex(toDynamicIndex(a)));
  endfunction
  function Bit#(7) toDynamicIndex(RegAddress a); 
    case(a) matches
      tagged Reg_Normal .t: return(zeroExtend(t));
      tagged Reg_SPR .pval: return(zeroExtend(pack(pval)) + 32);
      tagged Reg_SR     .t: return(zeroExtend(t) + 67);
    endcase
  endfunction
endinstance  
  
typedef union tagged {
  Bit#(5) CReg_Bit;
  Bit#(3) CReg_Field;
  void    CReg_All;
} CRegAddress deriving(Eq,Bits);

typedef union tagged {
  Bit#(1)  CVal_Bit;
  Bit#(4)  CVal_Field;
  Bit#(32) CVal_All;
} CRegValue deriving(Eq,Bits);

typedef union tagged {
  Tuple2#(Bit#(5),Bit#(1))  CWData_Bit;
  Tuple2#(Bit#(3),Bit#(4))  CWData_Field;
  Bit#(32)                  CWData_All;
} CRegWData deriving(Eq,Bits);


/********* Exceptions ***********************/

typedef enum {
  EX_External,   
  EX_InstStorage,
  EX_IllegalInst,
  EX_Privilege,
  Ex_IllegalInst,
  EX_FPUnavailable,   
  EX_FPAssist
} PPC_Exception deriving (Eq,Bits);
   
   

/********* Front End ***********************/

typedef enum
{
  FEX_External,    //TLB and so on
  FEX_InstStorage, //unaccessable memory
  FEX_IllegalInst
}  
  PPC_FrontEndException deriving (Eq, Bits);


typedef struct
{
  inst_addr_t iaddr;
  PPC_Instruction pinst;
  Maybe#(PPC_FrontEndException) exception;
} 
   PPC_InstBundle#(type inst_addr_t) deriving(Eq,Bits);

typedef struct
{
  Epoch       	      	     epoch;
  t          	      	     inst;
  iaddr_t    	      	     ia;
  Bool        	      	     pred;
  iaddr_t    	      	     nextia;
  Maybe#(PPC_FrontEndException)  exception;
} 
   PPC_Bundle#(type t, type iaddr_t) deriving (Bits, Eq);

typedef struct
{
  iaddr_t ia;
  Bool pred;
  iaddr_t real_next_ia;
  Bool wastaken;
}
  BranchPredUpdate#(type iaddr_t) deriving (Eq, Bits);
     
typedef Bit#(4)  CondFieldValue;

typedef struct 
{
  FUU_Op op;              //Op-specific info    
  op_T source3;           //used for rotates and floating
  op_T source2;
  op_T source1;
  tag_T tag;              //Tag given by CCU
} 
  FUUReq#(type tag_T, type op_T) deriving (Eq,Bits);


/***********************************************/
/* Functional Unit Result Type                 */
/***********************************************/

typedef enum
{
  FUUX_IllegalInst,     // 
  FUUX_PrivelegedInst,  //XXX  not used
  FUUX_FPUnavailable,   // no FP
  FUUX_FPAssist         // sw FP
}  
  FUUException deriving (Eq, Bits);

/*
typedef struct {
  Maybe#(Bit#(1)) ov;
  Maybe#(Bit#(1)) so;
  Maybe#(Bit#(1)) ca;
} XERRespValue deriving(Eq,Bits);

function Bit#(32) forgeNewXERValue(XERRespValue resp, Bit#(32) xer);
  return({isJust(resp.ov)?
                unJust(resp.ov):xer[31],
          isJust(resp.so)?
                unJust(resp.so):isJust(resp.ov)?unJust(resp.ov)|xer[30]:xer[30],
          isJust(resp.ca)?unJust(resp.ca):xer[29],
          xer[28:0]});
endfunction
*/

typedef struct {
  op_T value;
  CondValue cond;
  Maybe#(Bit#(1)) ov;
  Maybe#(Bit#(1)) ca;
  tag_T tag;
  Maybe#(FUUException) ex;
} FUUResponse#(type tag_T, type op_T) deriving (Eq,Bits);


typedef struct
{
  BRU_Op     op;
  Bit#(1)    cond;  //from source1
  op_T       disp;  //from source2
  op_T       ctr;   //from source3
  op_T       cur_pc;
  Bool       pred_taken;
  op_T       pred_pc;
  tag_T      tag;
} 
  BRUReq #(type tag_T, type op_T) 
      deriving
              (Eq,Bits);

typedef struct
{
  op_T     next_pc;
  op_T     ctr_val;   //dest1
  op_T     lr_val;    //dest2
  Bool     good_pred;
  Bool     taken;
  tag_T    tag;
}
  BRUResponse #(type tag_T, type op_T) 
      deriving
              (Eq,Bits);

typedef enum
{
  LSUX_DataStorage, 
  LSUX_Alignment
}  
  LSUException 
      deriving 
              (Eq, Bits);

typedef struct
{
  LSU_Op op;
  op_T   data_in;
  op_T   addr;
  op_T   offset;
  tag_T  tag;
} 
  LSURequest #(type tag_T, type op_T) 
      deriving 
              (Eq, Bits);

typedef struct
{
  op_T effectiveAddr;
  op_T returnVal;
  Maybe#(CondValue) cond;
  tag_T tag;
  Maybe#(LSUException) ex;
} 
  LSUResponse #(type tag_T, type op_T) 
      deriving 
              (Eq, Bits);


typedef struct
{ 
  LoadStore op;
  data_T writevalue;
  data_T addr;
  tag_T tag;
}
  DCacheRequest #(type tag_T, type data_T)
      deriving
              (Eq, Bits);

typedef struct
{
  data_T value;
  tag_T tag;
} 
  DCacheResponse #(type tag_T, type data_T)
      deriving
              (Eq, Bits);

/*********** Decoded Instruction **************/

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
  FloatingOptions  	FUU_floating;
  void  	      	FUU_move;
  void                  FUU_fmove;
  MulOptions		FUU_multiply;
  RotateOptions 	FUU_rotate_left;
  ShiftLeftOptions	FUU_shift_left;
  ShiftRightOptions	FUU_shift_right;
} 
  FUU_Op deriving(Eq,Bits);

/*************** Arith Subtypes ***************/
/*                                            */
/* Groups covered: add, neg, sub              */
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
  Bool carrying;
  Bool extended;
  Bool shifted;
  Bool oe;
}
 ArithOptions deriving (Eq,Bits);

/*************** Logic Subtypes *****************/
/*                                              */
/* Groups covered: and, or, nand, nor, xor, eqv */
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
}
 LogicOptions deriving (Eq,Bits);


/************** Compare Subtypes ****************/
/*                                              */
/* Groups covered: cmp, cmpl                    */
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
/*                                              */
/************************************************/

typedef struct
{
  Bool doubleword;
}
  CountLZOptions deriving (Eq,Bits);



/**************** Divide Subgroup ***************/
/*                                              */
/* Groups covered: div                          */
/*                                              */
/************************************************/

typedef struct 
{
  Bool doubleword;
  Bool unsign;
  Bool oe;
}
  DivOptions deriving (Eq,Bits);

/****************** ExtendSign ******************/
/*                                              */
/* Groups covered: exts                         */
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
}
  ExtendOptions deriving (Eq,Bits);
  
/***************** FloatingPoint ****************/
/*                                              */
/* Groups covered: f                            */
/*                                              */
/************************************************/

typedef enum
{
  F_abs, 
  F_add, 
  F_cfi, 
  F_cmp, 
  F_cti, 
  F_div, 
  F_madd, 
  F_mr, 
  F_nabs, 
  F_neg, 
  F_re, 
  F_rsp, 
  F_rsqrte, 
  F_msub, 
  F_mul, 
  F_nmadd, 
  F_nmsub, 
  F_sel, 
  F_sqrt, 
  F_sub
}
  FloatingOp deriving (Bits,Eq);

typedef struct 
{
  FloatingOp op;
  Bool doubleword;
  Bool round;
  Bool ordered;
}
  FloatingOptions deriving (Eq,Bits);
  


/******************* Multiply *******************/
/*                                              */
/* Groups covered: mul                          */
/*                                              */
/************************************************/

typedef struct 
{
  Bool doubleword;
  Bool unsign;
  Bool high;
  Bool oe;
}
  MulOptions deriving (Eq,Bits);

/******************* Rotate *********************/
/*                                              */
/* Groups covered: rl                           */
/*                                              */
/************************************************/

typedef struct 
{
  MaskX       mb; // These should be six bit for alignment. 
  MaskX       me;
  Bool        partialReplace; // Set when the operation may not completely overwrite old value
  Bool        doubleword;
}
  RotateOptions deriving (Eq,Bits);

/***************** ShiftLeft ********************/
/*                                              */
/* Groups covered: sl                           */
/*                                              */
/************************************************/

typedef struct 
{
  Bool doubleword;
}
  ShiftLeftOptions deriving (Eq,Bits);
  
/***************** ShiftRight *******************/
/*                                              */
/* Groups covered: sr                           */
/*                                              */
/************************************************/

typedef struct 
{
  Bool algebraic;
  Bool doubleword;
}
  ShiftRightOptions deriving (Eq,Bits);

/******************** Branch ********************/
/*                                              */
/* Groups covered: b, bc                        */
/*                                              */
/************************************************/

typedef struct
{
   BranchOptions options; //Unconditional branches are indicated here
   Bool absAddress;
} 
  BRU_Op deriving (Eq,Bits);
  
/******************* Load/Store *****************/
/*                                              */
/* Groups covered: l, s                         */
/*                                              */
/************************************************/

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
  LS_halfword_byte_reverse,
  LS_multiple_word,
  LS_string_word,
  LS_word,
  LS_word_byte_reverse
}
  LSType deriving (Eq,Bits);
  
typedef struct 
{
  LSType lstype;
  LSOp op; 
  Bool reserved_conditional; // for lwarx and swcx. and friends
  Bool algebraic;     // zero otherwise}
} LoadStore deriving (Eq,Bits);
  

/****************** DIO GROUP *******************/
/*                                              */
/* The group that talks to the data cache.      */
/*                                              */
/************************************************/

typedef union tagged
{
  void      LSU_dcbf;
  void      LSU_dcbi;
  void      LSU_dcbst;
  void      LSU_dcbt;
  void      LSU_dcbtst;
  void      LSU_dcbz;
  void      LSU_eciwx;
  void      LSU_ecowx;
  void      LSU_eieio;
  void      LSU_slbia;
  void      LSU_slbie;
  void      LSU_sync;
  void      LSU_tlbia;
  void      LSU_tlbie;
  void      LSU_tlbsync;
  LoadStore LSU_load_store;
}
  LSU_Op deriving (Eq, Bits);
  
/****************** TRAP GROUP ******************/
/*                                              */
/* The group of traps, system calls, and CCU    */
/* handled operations such as sync.             */
/*                                              */
/************************************************/

/******************** Trap **********************/
/*                                              */
/* Groups covered: td, tw                       */
/*                                              */
/************************************************/

typedef struct
{
  Bool doubleword;
  Bit#(5) options;
}
  TrapOptions deriving (Eq, Bits);

typedef union tagged
{
  void        TRAP_isync;
  void        TRAP_rfi;
  void        TRAP_sc;
  TrapOptions TRAP_t;
}
  TRAP_Op deriving (Eq, Bits);
  
/********** Decoded Instruction Type ************/
/*                                              */
/* The main decoded instruction type.           */
/* Unimplemented instructions will be handled   */
/* by the OS.                                   */
/*                                              */
/************************************************/

typedef union tagged
{ 
  void	      	DS_None;
  RegAddress    DS_Reg;
  FPRAddress    DS_FReg;
}
  PPC_Dest deriving(Eq, Bits);  

typedef union tagged
{ 
  void	      	OP_None;
  RegAddress    OP_Reg;
  CRegAddress   OP_Cond;
  FPRAddress    OP_FReg;
  Bit#(24)      OP_SImmediate;
  Bit#(24)      OP_UImmediate;

}
  PPC_Operand deriving(Eq, Bits);  

typedef struct 
{
  DecodedData         data;
  PPC_Dest            dest;
  PPC_Dest            dest2;
  Maybe#(CRegAddress) cdest;
  PPC_Operand         source1;
  PPC_Operand         source2;
  PPC_Operand         source3;
  Bool	      	      supervisor;
}
  PPC_DecInst deriving(Eq,Bits);

//For stores: source1: address, source2: offset, source3: data

typedef union tagged
{
  FUU_Op     DEC_FUU;
  LSU_Op     DEC_LSU;
  BRU_Op     DEC_BRU;
  TRAP_Op    DEC_TRAP;
  Bit#(32)   DEC_UNIMPLEMENTED;
  void       DEC_UNDEFINED;
}
  DecodedData deriving (Eq, Bits);

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


function DecodedData getOp(PPC_DecInst x);
  return (x.data);
endfunction



function Bool isStore(DecodedData data);
  
  return case (data) matches
    tagged DEC_LSU .lop:
      return case (lop) matches
        tagged LSU_load_store .ls:
	  return ls.op == LSStore;
	endcase;
      default:
        return False;
    endcase;
    
endfunction

/*************************************************************************************************/
/* Jump identity functions (for Branch Prediction)                                               */
/*************************************************************************************************/

function Bit#(32) jump405Location(Bit#(32) ia, Bit#(32) inst);
 case (inst[31:26])
    6'b010000: //bc
      begin
        let npc = ((inst[1]==1)?0:ia) + signExtend({inst[15:2],2'b00});
        return ((npc < ia) ? npc: (ia + 4));
      end
    6'b010010: //b
      return (((inst[1]==1)?0:ia) + signExtend({inst[25:2],2'b00}));
    default:
      return (ia + 4);//next inst
  endcase
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
