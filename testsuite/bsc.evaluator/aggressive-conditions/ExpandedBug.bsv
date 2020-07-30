import Vector::*;
import FIFO::*;

typedef Bit#(8) Token;
typedef Bit#(64) Addr;
typedef Bit#(5) PRName;
typedef Bit#(5) Opcode;
typedef Bit#(5) Immediate;
typedef Bit#(5) Cond;
typedef Bit#(5) Flags;

typedef Vector#(NumSrcMap, PRName) InstPhysSrc;

typedef struct
{
  Inst        ins;      // encoded instruction
  InstPhysSrc physSrc;  // physical source registers
  PRName      physDest; // physical destination register
}
  DecodedInst
    deriving (Eq, Bits);

typedef 5 NumSrc;    // number of source operands
typedef 4 NumSrcMap; // those that get mapped; others are non-reg ops

typedef Vector#(NumSrc, LogicalReg) InstSrc;
typedef struct
{
  Opcode      opcode;     // defines the operation
  InstSrc     src;        // source operands
  LogicalReg  dest;       // destination operand
  Immediate   imm;        // immediate value
  Cond        cond;       // condition code
  Flags       rflags;     // read flag mask (on RFLAGS)
  Flags       wflags;     // write flag mask (on RFLAGS)
}
  Inst
    deriving (Eq, Bits);


function Flags flagsClear();
  return 0;
endfunction

typedef Bit#(8)  RegData;  // smallest data item stored in register
typedef 8 NumRegDataItems; // number of RegData items per register

// register read is data + flags
typedef struct
{
  RegReadValueData data;  // register data part
  Flags            flags; // register flags part
}
  RegReadValue
    deriving (Eq, Bits);
    
typedef Vector#(NumRegDataItems, RegData) RegReadValueData;

typedef Bit#(5) RegName;
    
function Bool isMappedReg(LogicalReg lReg);
  return (lReg.name < 30) && (lReg.name != 0);
endfunction

typedef enum
{
  SUBREG_64, // 64-bit [63:0] full register, eg. RAX
  SUBREG_32, // 32-bit [31:0] sub-register,  eg. EAX
  SUBREG_16, // 16-bit [15:0] sub-register,  eg. AX
  SUBREG_8,  //  8-bit  [7:0] sub-register,  eg. AL
  SUBREG_8H, //  8-bit [15:8] sub-register,  eg. AH
  SUBREG_INVALID
}
  SubReg
    deriving (Eq, Bits);

typedef struct
{
  RegName name;   // full-size logical register
  SubReg  subreg; // sub-register specification
}
  LogicalReg
    deriving (Eq, Bits);


typedef Bit#(64) Value;      // native pipeline value
typedef struct
{
  Value data;  // register data part
  Flags flags; // register flags part
}
  RegValue
    deriving (Eq, Bits);

// input multiplexor for source operands
function Maybe#(RegValue) muxSource(Maybe#(RegValue) valueIn, LogicalReg lReg, Value imm);
  let valid = isJust(valueIn);
  let regValue = unJust(valueIn);
  let value = regValue.data;
  let flags = regValue.flags;

  case (lReg.name) matches
    0:
      begin
        valid = True;
        value = 0;
        flags = flagsClear();
      end
    30:
      begin
        valid = True;
        value = ~0;
        flags = flagsClear();
      end
    31:
      begin
        valid = True;
        value = imm;
        flags = flagsClear();
      end
  endcase

  regValue = RegValue {data: value, flags: flags};
  return valid ? tagged Valid regValue : Invalid;
endfunction

function Maybe#(RegValue) formatRegRead (LogicalReg lReg, Maybe#(RegReadValue) readData);
  let dataValid = isJust(readData);
  let regReadValue = unJust(readData);
  let flags = regReadValue.flags;
  RegReadValueData data = regReadValue.data;

  // SUBREG_8H wants bits 15:8 in bits 7:0
  if (lReg.subreg == SUBREG_8H)
  begin
    data[0] = data[1];
  end

  Bit#(NumRegDataItems) valid;
  // determine valid bytes
  valid = case (lReg.subreg) matches
    SUBREG_8:  return 8'b00000001;
    SUBREG_8H: return 8'b00000001;
    SUBREG_16: return 8'b00000011;
    SUBREG_32: return 8'b00001111;
    SUBREG_64: return 8'b11111111;
    default:   return 8'b00000000;
  endcase;

  // mask invalid bytes to 0
  for (Integer index = 0; index < valueOf(NumRegDataItems); index = index + 1)
  begin
    if (valid[index] == 0)
    begin
      data[index] = 'b0;
    end
  end

  // remap from array of bytes to 64-bit data type
  let regValue = RegValue {data: unpack(pack(data)), flags: flags};

  return dataValid ? tagged Valid regValue : Invalid;
endfunction

(* options="-aggressive-conditions" *)
(* synthesize *)

module mkTest ();


  Vector#(NumSrcMap, FIFO#(Maybe#(RegReadValue))) link_read = newVector();
  for (Integer i = 0; i < valueOf(NumSrcMap); i = i + 1)
  begin
    link_read[i] <- mkFIFO();
  end
  
  FIFO#(Tuple3#(Token, Tuple2#(Addr, DecodedInst), void)) waitingQ <- mkFIFO();
  let outQ <- mkFIFO(); //MIP: This stops bsc from optimizing away everything

  // finish execution: actual execution
  rule handleExec_Execute (True);

    match {.token, {.addr, .decIns}, .*} = waitingQ.first();

    // get values from the register file / bypass unit

    Value imm = signExtend(decIns.ins.imm);

    Vector#(NumSrc, LogicalReg) src = newVector();
    Vector#(NumSrcMap, PRName) physSrc = newVector();
    Vector#(NumSrc, Bool) isReadySrc = newVector();
    Vector#(NumSrc, RegValue) valueSrc = newVector();
    
    //For mapped operands
    for (Integer i = 0; i < valueOf(NumSrcMap); i = i + 1)
    begin
    
      src[i] = decIns.ins.src[i];
      physSrc[i] = decIns.physSrc[i];
      
      let readData = link_read[i].first();
      link_read[i].deq();
      
      Maybe#(RegValue) value = (isMappedReg(src[i])) ? formatRegRead(src[i], readData) : Invalid;
      //Maybe#(RegValue) value = (isMappedReg(src[i])) ? tagged Valid(?) : Invalid; //MIP: This version works fast with or without aggressive-conditions
      
      let final_value = muxSource(value, src[i], imm);
      isReadySrc[i] = isJust(final_value);
      valueSrc[i] = unJust(final_value);
    end

    //For unmapped operands
    for (Integer i = valueOf(NumSrcMap); i < valueOf(NumSrc); i = i + 1)
    begin
      src[i] = decIns.ins.src[i];

      let regValue = RegValue {data: unpack(0), flags: unpack(0)};
      Maybe#(RegValue) value = tagged Valid regValue;
  

      let final_value = muxSource(value, src[i], imm);
      isReadySrc[i] = isJust(final_value);
      valueSrc[i] = unJust(final_value);
      
    end

    outQ.enq(tuple4(src, physSrc, isReadySrc, valueSrc));
    
  endrule

endmodule
