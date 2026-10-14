package BaseTypes;

/**************************************/
/*              Imports               */
/**************************************/


import X86_Datatypes::*;
// no need for extensive ISA information, functional model will translate a lot of them

/***********************************************/
/*              "Final" Types                  */
/***********************************************/

/***********************************************/
// Trace buffer definition
/***********************************************/

typedef Bit#(5)    InstSize;
typedef Bit#(1)    BITM;
typedef Bit#(2)    BranchInfo;
typedef Bit#(1)    MODRM;
typedef Bit#(10)   OPCODE;

typedef Bit#(4)    TBReg0;
typedef Bit#(4)    TBReg1;
typedef Bit#(4)    TBReg2;

typedef Bit#(3)    TBSeg0;
typedef Bit#(3)    TBSeg1;

typedef Bit#(32)   IVAddr;
typedef Bit#(32)   IPAddr;
typedef Bit#(32)   D0VAddr;
typedef Bit#(32)   D0PAddr;
typedef Bit#(32)   D1VAddr;
typedef Bit#(32)   D1PAddr;

typedef Bit#(32)   DVAddr;
typedef Bit#(32)   DPAddr;


typedef struct {
  InstSize    instSize;
  BITM        bitm;
  BranchInfo  branchInfo;
  MODRM       modrm;
  OPCODE      opcode;
  TBReg0      reg0;
  TBReg1      reg1;
  TBReg2      reg2;
  TBSeg0      seg0;
  TBSeg1      seg1;
  IVAddr      ivaddr;
  IPAddr      ipaddr;
  D0VAddr     d0vadd;
  D0PAddr     d0padd;
  D1VAddr     d1vadd;
  D1PAddr     d1padd;
} TBTrace deriving (Eq, Bits);

// todo, predicate instruction

/***********************************************/
// Decode table definition
/***********************************************/

// Decode table definition
typedef Bit#(2)    MEM_RW;
typedef Bit#(1)    DES_SEL;
typedef Bit#(2)    UOP_ORD;
typedef Bit#(4)    DEReg0;
typedef Bit#(4)    DEReg1;
typedef Bit#(4)    DEReg2;
typedef Bit#(4)    DEReg3;
typedef Bit#(4)    DESeg0;
typedef Bit#(4)    DESeg1;
typedef Bit#(3)    ALU_OP;
typedef Bit#(3)    FPU_OP;

typedef Bit#(1)    ID;
typedef Bit#(1)    VIP;
typedef Bit#(1)    VIF;
typedef Bit#(1)    AC;
typedef Bit#(1)    VM;
typedef Bit#(1)    NT;
typedef Bit#(1)    IOPL;
typedef Bit#(1)    OF;
typedef Bit#(1)    DF;
typedef Bit#(1)    FIF;
typedef Bit#(1)    TF;
typedef Bit#(1)    SF;
typedef Bit#(1)    ZF;
typedef Bit#(1)    AF;
typedef Bit#(1)    PF;
typedef Bit#(1)    CF;
typedef Bit#(1)    RF;

// changed if to iff to avoid verilog key word
typedef struct {
  ID      id;
  VIP     vip;
  VIF     vif;
  AC      ac;
  VM      vm;
  NT      nt;
  IOPL    iopl;
  OF      of;
  DF      df;
  FIF     fif;
  TF      tf;
  SF      sf;
  ZF      zf;
  AF      af;
  PF      pf;
  CF      cf;
  RF      rf;
} FLAGS deriving (Eq, Bits);

typedef struct {
  MEM_RW      mem_rw;
  DES_SEL     des_sel;
  UOP_ORD     uop_ord;
  DEReg0      reg0;
  DEReg1      reg1;
  DEReg2      reg2;
  DEReg2      reg3;
  DESeg0      seg0;
  DESeg1      seg1;
  ALU_OP      alu_op;
  FPU_OP      fpu_op;
  FLAGS       flags_rd;
  FLAGS       flags_wr;
} DEInfo deriving (Eq, Bits);

/***********************************************/
// Instruction and Branch related type definition

typedef Tuple4#(IAddress, Bool, IAddress, Bool) BranchPredUpdate;

typedef Maybe#(a) Predicated #(type a);

typedef Bit#(32) Instruction;
typedef Bit#(SizeOf#(Instruction)) PackedInstruction;

typedef Bit#(5)  Epoch;
typedef Bit#(32) IAddress;

typedef Bit#(8) BranchTag;

typedef struct{
   BRU_Op op;
//   LImmediate immediate;
//   CondValue cond;
   IAddress curPC;
//   OperandValue cr;
   Bool predTaken;
   IAddress predNextPC;
   BranchTag tag;
   } BranchReq deriving(Eq,Bits);

typedef struct{
   Bool invalidBranchOption;
   Bool goodPred;
   Bool branchtaken;
   IAddress correctNextPC;
   BranchTag tag;
  } BranchResponse deriving(Eq,Bits);


/***********************************************/

// OperandValue only used for condition evaluation
typedef Bit#(16) OperandValue;
typedef Bit#(1)  CondValue;
//typedef Bit#(4)  CondFieldValue;
typedef Bit#(8)  FXUTag;
typedef FXUTag   FPUTag;

// instruction bundle with jump marked
typedef Tuple5#(Epoch, a, IAddress, Bool, IAddress) Bundle#(type a);

/***********************************************/
/* Functional Unit Instruction Type -          */
/*    This Misses a loads/stores/traps/moves   */
/*    and some other things. It DOES have      */
/*    floats however                           */
/***********************************************/

typedef struct{
 FXU_Op op;              //Op-specific info
// Bit#(1) carry;          //The value of the carry register
// added to track uop
 FXUTag tag;            //Tag given by CCU
// the following are irrelevant information to be passed on
 FXUCRRespValue fxucrval;
} FXUReq deriving (Eq,Bits);

typedef struct{
 FPU_Op op;              //Op-specific info
// Bit#(1) carry;          //The value of the carry register
 FPUTag tag;            //Tag given by CCU
// the following are irrelevant information to be passed on
 FPUCRRespValue fpucrval;
} FPUReq deriving (Eq,Bits);

/***********************************************/
/* Functional Unit Result Type                 */
/***********************************************/

/*
typedef struct {
  Maybe#(Bit#(1)) of;
  Maybe#(Bit#(1)) sf;
  Maybe#(Bit#(1)) zf;
  Maybe#(Bit#(1)) af;
  Maybe#(Bit#(1)) pf;
  Maybe#(Bit#(1)) cf;
} FXUCRRespValue deriving(Eq,Bits);
*/

typedef FLAGS FXUCRRespValue;

//-- not sure about this one
/*
function Bit#(32) forgeNewCRValue(FXUCRRespValue resp, Bit#(32) cr);
  return({isJust(resp.of)?
                unJust(resp.of):cr[31],
          isJust(resp.so)?
                unJust(resp.so):isJust(resp.ov)?unJust(resp.ov)|cr[30]:cr[30],
          isJust(resp.ca)?unJust(resp.ca):cr[29],
          cr[28:0]});
endfunction
*/

typedef struct{
// no need to pass back data
  FXUCRRespValue fxucrval;
  FXUTag tag;
  } FXUResponse deriving (Eq,Bits);

// temporarily treat all CR values to/from the execution units are the same
/*
typedef struct {
  Maybe#(Bit#(1)) zf;
  Maybe#(Bit#(1)) pf;
  Maybe#(Bit#(1)) cf;
} FPUCRRespValue deriving(Eq,Bits);
*/

typedef FXUCRRespValue FPUCRRespValue;

typedef struct{
  FPUCRRespValue fpucrval;
  FPUTag tag;
  } FPUResponse deriving (Eq,Bits);

typedef FXUTag LSUTag;

typedef struct{
  LSU_Op op;
  IVAddr   ivaddr;
  DVAddr   dvaddr;
  DVAddr   dpaddr;
  LSUTag tag;
} LSURequest deriving (Eq,Bits);

/*
typedef struct {
  Maybe#(Bit#(1)) of;
  Maybe#(Bit#(1)) sf;
  Maybe#(Bit#(1)) zf;
  Maybe#(Bit#(1)) af;
  Maybe#(Bit#(1)) pf;
  Maybe#(Bit#(1)) cf;
} LSUCRRespValue deriving(Eq,Bits);
*/

typedef FXUCRRespValue LSUCRRespValue;

typedef struct{
  Maybe#(IVAddr) effectiveAddr;
//  Maybe#(CondFieldValue)   cond;
  LSUCRRespValue xerval;
  LSUTag tag;
} LSUResponse deriving (Eq,Bits);

typedef LSUTag DCacheTag;

typedef struct{ //read before write
// byte mask default to all enable right now
  Bit#(8) wbytemask;
  Bool write;
  Bool read;
  DVAddr dvaddr;
  DPAddr dpaddr;
  DCacheTag tag;
 } DCacheRequest deriving(Eq,Bits);

typedef struct{ //read before write
  DCacheTag tag;
 } DCacheResponse deriving(Eq,Bits);

endpackage: BaseTypes

