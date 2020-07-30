
(* synthesize *)
(* always_enabled, always_ready *)
module sysTest_Path_AlwaysEn(Reg#(Bool));
   RWire#(Bool) rw <- mkRWire;

   method Action _write(Bool x);
      rw.wset(x);
   endmethod

   method Bool _read();
      case (rw.wget) matches
	 tagged Invalid: return False;
	 tagged Valid .x: return x;
      endcase
   endmethod
endmodule

