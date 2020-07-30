import ValueImports::*;
import ActionImports::*;
import ActionValueImports::*;

import StmtFSM::*;


// Interface for the DUT
interface DUT;
   method Bit#(32)  m1_narrow(Bit#(32) x);
   method Bit#(128) m1_wide(Bit#(128) x);
   method Bit#(64)  m1_poly(Bit#(64) x);

   method Action m2 (Bit#(128) w, Bit#(64) p);

   method ActionValue#(Bit#(32))  m3_narrow (Bit#(128) w, Bit#(64) p);
   method ActionValue#(Bit#(128)) m3_wide   (Bit#(128) w, Bit#(64) p);
   method ActionValue#(Bit#(64))  m3_poly   (Bit#(128) w, Bit#(64) p);

   method Action display_state();
endinterface

(* synthesize *)
module mkTestMethodsDUT (DUT);
   // test input from register
   Reg#(Bit#(32)) n <- mkReg(64);

   // test write to register
   Reg#(Bit#(32))  res_n <- mkReg(0);
   Reg#(Bit#(128)) res_w <- mkReg(0);
   Reg#(Bit#(64))  res_p <- mkReg(0);

   // test ffunc in condition
   method Bit#(32)  m1_narrow(Bit#(32) x) if (const_narrow == 17);
      return (and32(17, x));
   endmethod

   method Bit#(128) m1_wide(Bit#(128) x);
      return (and128(x, '1));
   endmethod

   method Bit#(64)  m1_poly(Bit#(64) x);
      return (andN('1, x));
   endmethod

   method Action m2 (Bit#(128) w, Bit#(64) p);
      tick();
      action_function(n,w,p,"m2");
   endmethod

   method ActionValue#(Bit#(32)) m3_narrow(Bit#(128) w, Bit#(64) p);
      Bit#(32) res <- av_narrow (w, p, n, "m3_narrow");
      $display("m3_narrow: %h", res);
      res_n <= res;
      return res;
   endmethod

   method ActionValue#(Bit#(128)) m3_wide(Bit#(128) w, Bit#(64) p);
      Bit#(128) res <- av_wide ("m3_wide", n, p, w);
      $display("m3_wide: %h", res);
      res_w <= res;
      return res;
   endmethod

   method ActionValue#(Bit#(64))  m3_poly(Bit#(128) w, Bit#(64) p);
      Bit#(64) res <- av_poly (p, "m3_poly", w, n);
      $display("m3_poly: %h", res);
      res_p <= res;
      return res;
   endmethod

   method Action display_state();
      $display(" res_n = %h", res_n);
      $display(" res_w = %h", res_w);
      $display(" res_p = %h", res_p);
   endmethod
endmodule

// ---------------

(* synthesize *)
module mkTestMethodsTB ();

   DUT d <- mkTestMethodsDUT;

   Bit#(128) w = const_wide;
   Bit#(64) p = {const_narrow, const_narrow};

   Stmt test_seq =
      seq
	 action
            Bit#(32) rn1 = d.m1_narrow (const_narrow);
	    $display(" m1_narrow = %h", rn1);
	 endaction
	 action
            Bit#(128) rw1 = d.m1_wide (w);
	    $display(" m1_wide = %h", rw1);
	 endaction
	 action
	    Bit#(64) rp1 = d.m1_poly (p);
	    $display(" m1_poly = %h", rp1);
	 endaction
	 d.m2(w, p);
	 action
	    let res <- d.m3_narrow(w,p);
	    $display(" m3_narrow = %h", res);
	 endaction
	 action
	    let res <- d.m3_wide(w,p);
	    $display(" m3_wide = %h", res);
	 endaction
	 action
	    let res <- d.m3_poly(w,p);
	    $display(" m3_poly = %h", res);
	 endaction
      endseq;
   
   FSM test_fsm <- mkFSM(test_seq);
   Reg#(Bool) going <- mkReg(False);

   rule start (!going);
      going <= True;
      test_fsm.start;
   endrule

   rule stop (going && test_fsm.done);
      $finish(0);
   endrule

   Reg#(UInt#(7)) watchdog <- mkReg(0);
   
   rule check_watchdog;
     if(watchdog > 100) begin
        $display("Watchdog check failed\n");
        $finish(0);
     end
     watchdog <= watchdog + 1;
   endrule

endmodule

