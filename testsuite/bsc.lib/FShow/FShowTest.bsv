import List   ::*;
import Vector ::*;
import FIFOF_ ::*;
import FIFOF  ::*;

import FShow  ::*;

typedef UInt#(8) U8;

(* synthesize *)
module sysFShowTest();

   Reg#(Bool) done <- mkReg(False);

   rule doDisplay(!done);

      $display("String");
      String s = "Hello";
      $display(fshow(s));

      $display("");

      $display("Char");
      Char c = "~";
      $display(fshow(c));

      $display("");

      $display("Bool");
      Bool f = False;
      Bool t = True;
      $display(fshow(f));
      $display(fshow(t));

      $display("");

      $display("Maybe");
      Maybe#(Bool) i = tagged Invalid;
      Maybe#(Bool) v = tagged Valid True;
      $display(fshow(i));
      $display(fshow(v));

      $display("");

      $display("Int");
      Int#(16) int1 = 17;
      $display(fshow(int1));

      $display("");

      $display("UInt");
      UInt#(32) uint1 = 42;
      $display(fshow(uint1));

      $display("");

      $display("Bit");
      Bit#(16) bit1 = 'hABCD;
      $display(fshow(bit1));

      $display("");

      $display("FIFOF_");
      FIFOF_#(UInt#(8)) emptyfifof_ =
         interface FIFOF_;
	    method notFull() = True;
	    method i_notFull() = True;
	    method notEmpty() = False;
	    method i_notEmpty() = False;
	    method first() = 1;
	    method enq(x) = noAction;
	    method deq() = noAction;
	    method clear() = noAction;
         endinterface;
      FIFOF_#(UInt#(8)) fullfifof_ =
         interface FIFOF_;
	    method notFull() = False;
	    method i_notFull() = False;
	    method notEmpty() = True;
	    method i_notEmpty() = True;
	    method first() = 2;
	    method enq(x) = noAction;
	    method deq() = noAction;
	    method clear() = noAction;
         endinterface;
      FIFOF_#(UInt#(8)) fifof_ =
         interface FIFOF_;
	    method notFull() = True;
	    method i_notFull() = True;
	    method notEmpty() = True;
	    method i_notEmpty() = True;
	    method first() = 3;
	    method enq(x) = noAction;
	    method deq() = noAction;
	    method clear() = noAction;
         endinterface;
      $display(fshow(emptyfifof_));
      $display(fshow(fullfifof_));
      $display(fshow(fifof_));
      $display("");

      $display("FIFOF");
      FIFOF#(UInt#(8)) emptyfifof =
         interface FIFOF;
	    method notFull() = True;
	    method notEmpty() = False;
	    method first() = 1;
	    method enq(x) = noAction;
	    method deq() = noAction;
	    method clear() = noAction;
         endinterface;
      FIFOF#(UInt#(8)) fullfifof =
         interface FIFOF;
	    method notFull() = False;
	    method notEmpty() = True;
	    method first() = 2;
	    method enq(x) = noAction;
	    method deq() = noAction;
	    method clear() = noAction;
         endinterface;
      FIFOF#(UInt#(8)) fifof =
         interface FIFOF;
	    method notFull() = True;
	    method notEmpty() = True;
	    method first() = 3;
	    method enq(x) = noAction;
	    method deq() = noAction;
	    method clear() = noAction;
         endinterface;
      $display(fshow(emptyfifof));
      $display(fshow(fullfifof));
      $display(fshow(fifof));
      $display("");

      $display("Vector");
      Vector#(0, Bit#(8)) v0 = Vector::map(fromInteger, genVector);
      Vector#(1, Bit#(8)) v1 = Vector::map(fromInteger, genVector);
      Vector#(4, Bit#(8)) v4 = Vector::map(fromInteger, genVector);
      $display(fshow(v0));
      $display(fshow(v1));
      $display(fshow(v4));
      $display("");

      // XXX This is an abstract type with no creation functions defined,
      // XXX so the only way to create a value is to unpack from bits.
      $display("Ascii");
      Ascii#(0) a0 = unpack(0);
      Ascii#(2) a2 = unpack({8'd72, 8'd105}); // "Hi"
      $display(fshow(a0));
      $display(fshow(a2));
      $display("");

      $display("List");
      List#(Bit#(8)) s0 = List::nil;
      List#(Bit#(8)) s1 = List::map(fromInteger, List::upto(0,0));
      List#(Bit#(8)) s4 = List::map(fromInteger, List::upto(0,3));
      $display(fshow(s0));
      $display(fshow(s1));
      $display(fshow(s4));
      $display("");

      $display("Tuples");
      Tuple2#(U8,U8) t2 = tuple2(0,1);
      Tuple3#(U8,U8,U8) t3 = tuple3(0,1,2);
      Tuple4#(U8,U8,U8,U8) t4 = tuple4(0,1,2,3);
      Tuple5#(U8,U8,U8,U8,U8) t5 = tuple5(0,1,2,3,4);
      Tuple6#(U8,U8,U8,U8,U8,U8) t6 = tuple6(0,1,2,3,4,5);
      Tuple7#(U8,U8,U8,U8,U8,U8,U8) t7 = tuple7(0,1,2,3,4,5,6);
      Tuple8#(U8,U8,U8,U8,U8,U8,U8,U8) t8 = tuple8(0,1,2,3,4,5,6,7);
      $display(fshow(t2));
      $display(fshow(t3));
      $display(fshow(t4));
      $display(fshow(t5));
      $display(fshow(t6));
      $display(fshow(t7));
      $display(fshow(t8));
      $display("");

      $display("Fmt");
      Fmt fmt0 = $format("ThisIsAString");
      $display(fshow(fmt0));

      done <= True;
   endrule

   rule doFinish(done);
      $finish(0);
   endrule

endmodule

