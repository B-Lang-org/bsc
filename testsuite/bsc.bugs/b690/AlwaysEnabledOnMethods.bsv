
interface Foo;
  method Action do_foo();
  interface Reg#(int) the_reg;
endinterface

(* synthesize, always_enabled = "the_reg._write" *)
module mkAEFoo (Foo);

  Reg#(int) r <- mkReg(0);
  
  method Action do_foo();
    r <= 0;
  endmethod
  
  interface Reg the_reg;
    method Action _write(int x);
      r <= x - 1;
    endmethod
    
    method int _read();
      return r + 1;
    endmethod
  endinterface

endmodule

(* synthesize *)
module mkAETest ();

  Foo foo <- mkAEFoo;
  
  rule alwaysEn (True);
    foo.the_reg._write(1 - foo.the_reg._read);
  endrule
endmodule

