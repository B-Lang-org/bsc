interface IFC;
   method Bool m1;
   method Bool m2;
endinterface

function Bool getWithDefault(Maybe#(Bool) x);
   case (x) matches
      tagged Invalid : return True;
      tagged Valid .a : return a;
   endcase
endfunction
   
(* synthesize *)
module mkValueMethodEx2Mod1 (IFC);
   Reg#(Bool) rg <- mkRegU;
   RWire#(Bool) rw <- mkRWire;

   rule r;
      rg <= True;
      rw.wset(True);
   endrule

   method m1 = rg;
   method m2 = getWithDefault(rw.wget);
endmodule

(* synthesize *)
module mkValueMethodEx2Mod2 (IFC);
   Reg#(Bool) rg <- mkRegU;
   RWire#(Bool) rw <- mkRWire;

   rule r;
      rg <= True;
      rw.wset(True);
   endrule

   method m1 if (rg);
      return True;
   endmethod

   method m2 if (getWithDefault(rw.wget));
      return False;
   endmethod
endmodule
