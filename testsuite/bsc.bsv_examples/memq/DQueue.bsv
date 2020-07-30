package DQueue;

// This package implements a queue with entries of the prescribed structure.

import QType::*;
import DQueueConfig::*;
import PriQ::*;
import Priority::*;

// In the definitions which follow, the types of fields which have
// sub-structure have been given names, while those that do not have usually
// been left as "Bit" types.  This could of course be changed.

typedef struct {
   Bit#(WRAP_SIZE) wrap;
   Bit#(RW_SIZE) rw;
		} Command_type deriving(Eq, Bits);

// All these types must be representable as bits, and testable for equality.
// If we are content for the tool to use the obvious definitions, we tell it
// to do so using the "deriving" feature, as above.

// The components of the page address structure.
typedef Bit#(CS_SIZE) Cs;
typedef Bit#(ROW_SIZE) Row;
typedef Bit#(BANK_SIZE) Bank;

typedef struct {
   Cs cs;
   Row row;
   Bank bank;
		} Page deriving(Eq);

// For the Page type it is OK to use the obvious definition of Equality; but
// we wish to parameterize how the structure is packed into bits.  Accordingly
// we do not use "deriving" for this, but set the whole thing out explicitly,
// by defining this "instance" of the "Bits" typeclass.  The "pack" function
// converts the struct type to a bit-pattern; the "unpack" function does the
// converse.  The particular packing is chosen by case-switch on an Integer
// parameter defined in the DQueueConfig package.

instance Bits#(Page, sz)
   provisos (Add#(CS_SIZE, ROW_SIZE, k), Add#(k, BANK_SIZE, sz));
   function pack(p);
      function p123(c,r,b) = pack(tuple3(c,r,b));
      function p231(c,r,b) = pack(tuple3(r,b,c));
      function p312(c,r,b) = pack(tuple3(b,c,r));
      function p132(c,r,b) = pack(tuple3(c,b,r));
      function p321(c,r,b) = pack(tuple3(b,r,c));
      function p213(c,r,b) = pack(tuple3(r,c,b));
      match tagged Page{cs: .c, row: .r, bank: .b} = p;
      case (page_packing)
	 123: return p123(c,r,b);
	 231: return p231(c,r,b);
	 312: return p312(c,r,b);
	 132: return p132(c,r,b);
	 321: return p321(c,r,b);
	 213: return p213(c,r,b);
	 default: return(error("invalid page_packing value"));
      endcase
   endfunction
   function unpack(x);
      function u123(bs);
	 match {.c,.r,.b} = Tuple3#(Cs,Row,Bank)'(unpack(bs));
	 return (Page{cs: c, row: r, bank: b});
      endfunction
      function u231(bs);
	 match {.r,.b,.c} = Tuple3#(Row,Bank,Cs)'(unpack(bs));
	 return (Page{cs: c, row: r, bank: b});
      endfunction
      function u312(bs);
	 match {.b,.c,.r} = Tuple3#(Bank,Cs,Row)'(unpack(bs));
	 return (Page{cs: c, row: r, bank: b});
      endfunction
      function u132(bs);
	 match {.c,.b,.r} = Tuple3#(Cs,Bank,Row)'(unpack(bs));
	 return (Page{cs: c, row: r, bank: b});
      endfunction
      function u321(bs);
	 match {.b,.r,.c} = Tuple3#(Bank,Row,Cs)'(unpack(bs));
	 return (Page{cs: c, row: r, bank: b});
      endfunction
      function u213(bs);
	 match {.r,.c,.b} = Tuple3#(Row,Cs,Bank)'(unpack(bs));
	 return (Page{cs: c, row: r, bank: b});
      endfunction
      case (page_packing)
	 123: return u123(x);
	 231: return u231(x);
	 312: return u312(x);
	 132: return u132(x);
	 321: return u321(x);
	 213: return u213(x);
	 default: return(error("invalid page_packing value"));
      endcase
   endfunction
endinstance

// Then the Page definition is used in the Address definition, which in turn
// is used in the Entry definition.

typedef struct {
   Page page;
   Bit#(COL_SIZE) col;
   Bit#(B_SIZE) b;
		} Address deriving(Eq, Bits);

typedef struct {
   Address address;
   Bit#(LENGTH_SIZE) length;
   Command_type command_type;
   Priority#(PRIORITY_SIZE) prio;
   Bit#(SOURCE_ID_SIZE) source_id;
   Bit#(BUFF_ID_SIZE) buff_id;
		} Entry deriving(Eq, Bits);

// It is convenient to have a skeleton Entry value defined.

Entry empty_entry = unpack(0);

// For the purposes of the priority queue, we now define an ordering on
// Entries.  We have chosen to base this on the priority field; within the
// same priority reads (rw=0) take precedence over writes (rw=1).  (This is
// only for the sake of example: an eventual ordering criterion would probably
// be much more complicated than this.)

instance Ord#(Entry);
   function \< (e1,e2);
      let t1 = tuple2(e1.prio, invert(e1.command_type.rw));
      let t2 = tuple2(e2.prio, invert(e2.command_type.rw));
      return (t1 < t2);
   endfunction
   function \<= (e1,e2);
      let t1 = tuple2(e1.prio, invert(e1.command_type.rw));
      let t2 = tuple2(e2.prio, invert(e2.command_type.rw));
      return (t1 <= t2);
   endfunction
   function \> (e1,e2);
      let t1 = tuple2(e1.prio, invert(e1.command_type.rw));
      let t2 = tuple2(e2.prio, invert(e2.command_type.rw));
      return (t1 > t2);
   endfunction
   function \>= (e1,e2);
      let t1 = tuple2(e1.prio, invert(e1.command_type.rw));
      let t2 = tuple2(e2.prio, invert(e2.command_type.rw));
      return (t1 >= t2);
   endfunction
endinstance

// Having defined the Entry type, we can define a module to produce the
// particular kind of queue we want, and it can be synthesized to RTL.  (Note
// that the definition in PriQ.bsv cannot be synthesized, as it are not tied
// down to a particular entry type "qe" -- so, for example, it is not known at
// that stage how wide the ports must be.)

(* synthesize *)
module mkQueue(Q#(Entry));
   let queue <- mkSizedPriQ(pipelining, queue_length);
   return queue;
endmodule

endpackage
