package EthFrame;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

import Util::*;
import GetPut::*;
import BGetPut::*;
import Connectable::*;
import Randomizeable::*;
import Control::*;
import Vector::*;
import RandomSynth::*;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

typedef 50 MaxDataLength;
typedef Vector#(MaxDataLength, Bit#(8)) DataVector;
typedef Bit#(16) DataSize;

typedef Bit#(3)  UserPriority;
typedef Bit#(12) FrameId;
typedef Bit#(48) FrameAddr;
typedef Bit#(16) FramePause;


typedef enum {UNTAGGED, TAGGED, CONTROL} FrameFormat deriving(Bounded, Bits, Eq);

typedef enum {IGNORE, PAUSE} FrameOpCode deriving(Bounded, Bits, Eq);

typedef struct {
		DataSize    size;
		DataVector  data;
		} FrameData  deriving (Bounded, Bits, Eq);


typedef struct {
		FrameId      id;
		FrameAddr    src;
		FrameAddr    dst;
		FrameFormat  format;
		UserPriority user_priority;
		Bool         cfi;
		FrameOpCode  opcode;
		FramePause   pause_time;
		FrameData    data;
		} Frame  deriving (Eq);

//typedef TAdd#(184, TMul#(8, MaxDataLength)) FrameBitSize;
typedef TAdd#(200, TMul#(8, MaxDataLength)) FrameBitSize;


////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface FrameTxRxIFC;
   interface Get#(Frame) tx;
   interface Put#(Frame) rx;
endinterface

interface BFrameTxRxIFC;
   interface BGet#(Frame) tx;
   interface BPut#(Frame) rx;
endinterface

interface FrameBTxRxIFC;
   interface BGet#(Frame) tx;
   interface Put#(Frame) rx;
endinterface

interface FrameTxBRxIFC;
   interface Get#(Frame) tx;
   interface BPut#(Frame) rx;
endinterface

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

instance Connectable#(FrameTxRxIFC, FrameTxRxIFC);
      module mkConnection#(FrameTxRxIFC left, FrameTxRxIFC right) (Empty);
	 mkConnection(left.tx, right.rx);
	 mkConnection(left.rx, right.tx);
      endmodule
endinstance

instance Connectable#(BFrameTxRxIFC, BFrameTxRxIFC);
      module mkConnection#(BFrameTxRxIFC left, BFrameTxRxIFC right) (Empty);
	 mkConnection(left.tx, right.rx);
	 mkConnection(left.rx, right.tx);
      endmodule
endinstance

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

function String showFrameOpCode (FrameOpCode opcode);

   String result;
   
   case (opcode)
      PAUSE: result = "PAUSE";
      IGNORE: result = "IGNORE";
      default: result = "INVALID";
   endcase
   return result;

endfunction


function String showFrameFormat (FrameFormat format);

   String result;
   
   case (format)
      UNTAGGED: result = "UNTAGGED";
      TAGGED: result = "TAGGED";
      CONTROL: result = "CONTROL";
      default: result = "INVALID";
   endcase
   return result;

endfunction


////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

function String showFrame (Frame frame);

   return strConcat("[FRAME",
	  strConcat(
	  strConcat(
		    strConcat(
			      strConcat(" opcode: ", 
					(bitToString (pack(frame.opcode)))),
			      strConcat(",\n                  id: ", 
					(bitToString (pack(frame.id))))),
		    strConcat(
			      strConcat(",\n                 src: ", 
					(bitToString (pack(frame.src)))),
			      strConcat(",\n                 dst: ", 
					(bitToString (pack(frame.dst)))))),
		    "]"));
endfunction

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

function Action displayFrame (Frame frame);
   if (frame.opcode == PAUSE)
      $display("[FRAME opcode: %0s\n   pause_time: %d\n          src: %h\n          dst: %h\n       format: %0s\n]",
	       showFrameOpCode(frame.opcode), 
	       frame.pause_time,
	       frame.src,
	       frame.dst,
	       showFrameFormat(frame.format)
	       );
   else
      begin
	 Bit#(64) value = grab_left(frame.data.data);
	 $display("[FRAME opcode: %0s\n           id: %d\n          src: %h\n          dst: %h\n       format: %0s\n         size: %d\n         data: %h ....\n]",
	       showFrameOpCode(frame.opcode), 
	       frame.id,
	       frame.src,
	       frame.dst,
	       showFrameFormat(frame.format),
	       frame.data.size,
	       value
		  );
      end

endfunction

////////////////////////////////////////////////////////////////////////////////
/// Create a frame factory with fixed src/dst addresses.
////////////////////////////////////////////////////////////////////////////////

module mkFixedSrcDstRandomizer#(FrameAddr src_addr, FrameAddr dst_addr) (Randomize#(Frame));

   Randomize#(Frame) frame_gen <- mkRandomizer;

   interface Control cntrl;
      method Action init();
	 frame_gen.cntrl.init();
      endmethod
   endinterface

   method ActionValue#(Frame) next ();
      let frame <- frame_gen.next();
      frame.src = src_addr;
      frame.dst = dst_addr;
      return frame;
   endmethod
   
endmodule

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

instance Randomizeable#(Frame);
      module mkRandomizer (Randomize#(Frame));
	 
	 Reg#(FrameId) id_count <- mkReg(0);

	 Randomize#(FrameAddr) src_gen <- mkGenericRandomizer_Synth;
	 Randomize#(FrameAddr) dst_gen <- mkGenericRandomizer_Synth;
	 Randomize#(FrameData) data_gen <- mkRandomizer;
	 Randomize#(FrameFormat) format_gen <- mkGenericRandomizer_Synth;
	 Randomize#(FramePause) pause_gen <- mkConstrainedRandomizer_Synth(1,3);

	 interface Control cntrl;
	    method Action init();
	       src_gen.cntrl.init();
	       dst_gen.cntrl.init();
	       data_gen.cntrl.init();
	       format_gen.cntrl.init();
	       pause_gen.cntrl.init();
	    endmethod
	 endinterface
	 
	 method ActionValue#(Frame) next ();
   
	    let src <- src_gen.next();
	    let dst <- dst_gen.next();
	    let format <- format_gen.next();
	    let pause_time <- pause_gen.next();
	    
	    FrameData data;
	    FrameOpCode opcode;
	    
	    case (format)
	       CONTROL: begin
			   data = unpack(0);
			   opcode = PAUSE;
			end
	       default: begin
			   data <- data_gen.next();
			   opcode = IGNORE;
			end
	       
	    endcase

	    let frame = Frame {id:            id_count,
			       src:           src,
			       dst:           dst,
			       format:        format,
			       user_priority: 0,
			       cfi:           False,
			       opcode:        opcode,
			       pause_time:    pause_time,
			       data:          data
			       };

	    id_count <= id_count + 1;

	    
	    let byte_size = getFrameByteSize(frame);
	    let delta = fromInteger(getSizeOf(frame)) - (8 * byte_size);

	    Bit#(FrameBitSize) shifted = (pack(frame) >> delta) << delta;

	    return unpack(shifted);
	    
	 endmethod

      endmodule
endinstance

instance Randomizeable#(FrameData);
      module mkRandomizer (Randomize#(FrameData));

	 let max = fromInteger(valueOf(MaxDataLength));
	 
	 Randomize#(DataSize) size_gen <- mkConstrainedRandomizer_Synth(0, max - 1);
	 Randomize#(DataVector) data_gen <- mkGenericRandomizer_Synth;

	 interface Control cntrl;
	    method Action init();
	       size_gen.cntrl.init();
	       data_gen.cntrl.init();
	    endmethod
	 endinterface

	 method ActionValue#(FrameData) next ();

	    let size <- size_gen.next();
	    let data <- data_gen.next();

	    let out = FrameData {size: size,
				 data: data
				 };
	    
	    return out;
	 endmethod
	 
      endmodule
endinstance      

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

function Bit#(16) getFrameByteSize(Frame frame);
   if (frame.format == TAGGED)
      return 14 + frame.data.size + 4;
   else
      return 14 + frame.data.size;
endfunction
      
////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

function Frame remove_trailing_data(Frame frame);
	 
   let byte_size = getFrameByteSize(frame);
   let delta = fromInteger(getSizeOf(frame)) - (8 * byte_size);
   
   Bit#(FrameBitSize) shifted = (pack(frame) >> delta) << delta;

   return unpack(shifted);
endfunction


instance Bits#(Frame, FrameBitSize)
   provisos(Add#(ignore, 48, FrameBitSize));
  
   function Bit#(FrameBitSize) pack(Frame frame);

      let offset = 0;

      Bit#(FrameBitSize) frame_bytes;

      case (tuple2(frame.format, frame.opcode)) matches
	 {UNTAGGED,     .*}: frame_bytes = {frame.dst, frame.src, frame.data.size, pack(frame.data.data), 0};
	 {  TAGGED,     .*}: frame_bytes = {frame.dst, frame.src, 16'h8100, frame.user_priority, pack(frame.cfi), frame.id, frame.data.size, pack(frame.data.data), 0};
	 { CONTROL,  PAUSE}: frame_bytes = {frame.dst, frame.src, 16'h8808, 16'h0001, frame.pause_time, 0};
	 { CONTROL,     .*}: frame_bytes = {frame.dst, frame.src, 16'h8808, 16'h0000, 0};
	            default: frame_bytes = {0};
      endcase
   
      return frame_bytes;
   endfunction
   
   function Frame unpack(Bit#(FrameBitSize) frame_bits);

      Bit#(FrameBitSize) current;
      Bit#(16) format_bytes;

      FrameId id = 0;
      FrameAddr dst;
      FrameAddr src;
      FrameFormat format;
      UserPriority user_priority = 0;
      Bool cfi = False;
      FrameOpCode opcode = IGNORE;
      FramePause pause_time = 0;

      DataSize size = 0;
      DataVector data = unpack(0);

      current = frame_bits;

      dst = grab_left(current);

      current = current << fromInteger(getSizeOf(dst));

      src = grab_left(current);

      current = current << fromInteger(getSizeOf(src));

      format_bytes = grab_left(current);

      case (format_bytes)
	 16'h8100: begin
		      current = current << fromInteger(getSizeOf(format_bytes));
		      format = TAGGED;
		      user_priority = grab_left(current);
		      current = current << fromInteger(getSizeOf(user_priority));
		      cfi = grab_left(current);
		      current = current << fromInteger(getSizeOf(cfi));
		      id = grab_left(current);
		      current = current << fromInteger(getSizeOf(id));
		   end
	 16'h8808: begin
		      current = current << fromInteger(getSizeOf(format_bytes));
		      format = CONTROL;
		      Bit#(16) opcode_bytes;
                      opcode_bytes = grab_left(current);
		      current = current << fromInteger(getSizeOf(opcode_bytes));
		      if (opcode_bytes == 16'h0001)
			 begin
			    opcode = PAUSE;
			    pause_time = grab_left(current);
			    current = current << fromInteger(getSizeOf(pause_time));
			 end
		   end
	 default: begin
		     format = UNTAGGED;
		  end
      endcase

      case (format)
	 TAGGED, UNTAGGED: begin
	    size = grab_left(current);
	    current = current << fromInteger(getSizeOf(size));
	    data = grab_left(current);
	    current = current << fromInteger(getSizeOf(data));
	 end
      endcase
   
      
      let frame_data = FrameData {size: size,
				  data: data
				  };
	    
      let frame = Frame {id:            id,
			 src:           src,
			 dst:           dst,
			 format:        format,
			 user_priority: user_priority,
			 cfi:           cfi,
			 opcode:        opcode,
			 pause_time:    pause_time,
			 data:          frame_data
			 };

      return frame;
   endfunction
endinstance
      
////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

function Bit#(32) calculatePortAddress(Integer count, Frame frame);
   
   if (count < 2)
      return 0;
   else if (count < 3)
      begin
	 Bit#(1) value;
	 value = truncate(frame.dst);
	 return {0, min(fromInteger(count - 1), value)};
      end
   else if (count < 5)
      begin
	 Bit#(2) value;
	 value = truncate(frame.dst);
	 return {0, min(fromInteger(count - 1), value)};
      end
   else if (count < 9)
      begin
	 Bit#(3) value;
	 value = truncate(frame.dst);
	 return {0, min(fromInteger(count - 1), value)};
      end
   else if (count < 17)
      begin
	 Bit#(4) value;
	 value = truncate(frame.dst);
	 return {0, min(fromInteger(count - 1), value)};
      end
   else 
      return (error("More than 16 ports not handled."));
	      
endfunction
      
endpackage


