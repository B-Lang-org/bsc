typedef enum { A, BC, D, E } Foo deriving(Eq, Bits);

typeclass Show#(type t);
   function String show(t value);
endtypeclass

instance Show#(Foo);
   function show(f);
     case (f) matches
       A: return "A";
       BC: return "BC";
       D: return "D";
     endcase
   endfunction
endinstance

(* synthesize *)
module sysUndefinedString();

  Reg#(Foo) r <- mkReg(A);

  rule test;
    $display(show(r));
    r <= (case (r) matches
           A: return BC;
           BC: return D;
           D: return E;
          endcase);
    if (r == E) begin
      Foo f = ?;
      $display(show(f));
      $finish(0);
    end
  endrule
endmodule


 