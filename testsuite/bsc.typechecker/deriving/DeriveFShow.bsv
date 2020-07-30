import FShow :: *;

// Test an isomorphic tagged union
typedef union tagged { Bit#(8) IsoU; } IsoU deriving (FShow);
// Test a polymorphic version
typedef union tagged { Bit#(n) IsoUP; } IsoUP#(type n) deriving (FShow);
// Test a fully polymorphic version
typedef union tagged { t IsoUFP; } IsoUFP#(type t) deriving (FShow);

// Test an isomorhphic struct
typedef struct { Int#(16) isoS; } IsoS deriving (FShow);
// Test a polymorphic version
typedef struct { Int#(n) isoSP; } IsoSP#(type n) deriving (FShow);
// Test a fully polymorphic version
typedef struct { t isoSFP; } IsoSFP#(type t) deriving (FShow);

// Test an enum
typedef enum { Enum0, Enum1, Enum2 } BasicE deriving (FShow);

// Test a tagged union of basic types
typedef union tagged {
   Bool      BasicU0;
   Bit#(8)   BasicU1;
   UInt#(16) BasicU2;
   Int#(32)  BasicU3;
} BasicU deriving (FShow);
// Test a polymorphic version
typedef union tagged {
   t1        BasicUP0;
   Bit#(n1)  BasicUP1;
   UInt#(n2) BasicUP2;
   Int#(n3)  BasicUP3;
   t2        BasicUP4;
} BasicUP#(type n1, type n2, type n3, type t1, type t2) deriving (FShow);

// Test a struct of basic types
typedef struct {
   Bool      basicS0;
   Bit#(8)   basicS1;
   UInt#(16) basicS2;
   Int#(32)  basicS3;
} BasicS deriving (FShow);
// Test a polymorphic version
typedef struct {
   t1        basicSP0;
   Bit#(n1)  basicSP1;
   UInt#(n2) basicSP2;
   Int#(n3)  basicSP3;
   t2        basicSP4;
} BasicSP#(type n1, type n2, type n3, type t1, type t2) deriving (FShow);

// Test a tagged union containing enum/union/struct
typedef union tagged {
   BasicE NestedU0;
   BasicU NestedU1;
   BasicS NestedU2;
} NestedU deriving (FShow);
// Test a polymorphic version
typedef union tagged {
   BasicE                       NestedUP0;
   BasicUP#(n1, n2, n3, t1, t2) NestedUP1;
   BasicSP#(n1, n2, n3, t1, t2) NestedUP2;
} NestedUP#(type n1, type n2, type n3, type t1, type t2) deriving (FShow);

// Test a struct containing enum/union/struct
typedef struct {
   BasicE nestedS0;
   BasicU nestedS1;
   BasicS nestedS2;
} NestedS deriving (FShow);
// Test a polymorphic version
typedef struct {
   BasicE                       nestedSP0;
   BasicUP#(n1, n2, n3, t1, t2) nestedSP1;
   BasicSP#(n1, n2, n3, t1, t2) nestedSP2;
} NestedSP#(type n1, type n2, type n3, type t1, type t2) deriving (FShow);

// Test a tagged union with some void data
typedef union tagged {
   void SomeVoidU0;
   Bool SomeVoidU1;
} SomeVoidU deriving (FShow);
// Test a tagged union with all void data
// (does it get displayed like an enum?)
typedef union tagged {
   void AllVoidU0;
   void AllVoidU1;
} AllVoidU deriving (FShow);

// Test a struct with no fields
typedef struct {
} EmptyS deriving (FShow);


(* synthesize *)
module sysDeriveFShow();
   Reg#(Bool) done <- mkReg(False);

   rule doDisplay(!done);

      $display("Isomorphic tagged union");
      IsoU iu1 = tagged IsoU 17;
      IsoUP#(16) iu2 = tagged IsoUP 42;
      IsoUFP#(Int#(32)) iu3 = tagged IsoUFP -2;
      $display(fshow(iu1));
      $display(fshow(iu2));
      $display(fshow(iu3));

      $display("");

      $display("Isomorphic struct");
      IsoS is1 = IsoS { isoS: 17 };
      IsoSP#(16) is2 = IsoSP { isoSP: 42 };
      IsoSFP#(Int#(32)) is3 = IsoSFP { isoSFP: -2 };
      $display(fshow(is1));
      $display(fshow(is2));
      $display(fshow(is3));

      $display("");

      $display("Basic enum");
      BasicE be0 = Enum0;
      BasicE be1 = Enum1;
      BasicE be2 = Enum2;
      $display(fshow(be0));
      $display(fshow(be1));
      $display(fshow(be2));
      $display("");

      $display("Basic tagged union");
      BasicU bu0 = tagged BasicU0 True;
      BasicU bu1 = tagged BasicU1 22;
      BasicU bu2 = tagged BasicU2 'hABCD;
      BasicU bu3 = tagged BasicU3 -'hABCD;
      BasicUP#(8,16,32,Bool,BasicE) bup0 = tagged BasicUP0 True;
      BasicUP#(8,16,32,Bool,BasicE) bup1 = tagged BasicUP1 22;
      BasicUP#(8,16,32,Bool,BasicE) bup2 = tagged BasicUP2 'hABCD;
      BasicUP#(8,16,32,Bool,BasicE) bup3 = tagged BasicUP3 -'hABCD;
      BasicUP#(8,16,32,Bool,BasicE) bup4 = tagged BasicUP4 Enum2;
      $display(fshow(bu0));
      $display(fshow(bu1));
      $display(fshow(bu2));
      $display(fshow(bu3));
      $display(fshow(bup0));
      $display(fshow(bup1));
      $display(fshow(bup2));
      $display(fshow(bup3));
      $display(fshow(bup4));

      $display("");

      $display("Basic struct");
      BasicS bs1 =
          BasicS { basicS0: True, basicS1: 22,
                   basicS2: 'hABCD, basicS3: -'hABCD };
      BasicSP#(8,16,32,Bool,BasicE) bsp1 =
          BasicSP { basicSP0: True, basicSP1: 22,
                    basicSP2: 'hABCD, basicSP3: -'hABCD,
                    basicSP4: Enum2 };
      $display(fshow(bs1));
      $display(fshow(bsp1));

      $display("");

      $display("Nested tagged union");
      NestedU nu0 = tagged NestedU0 be0;
      NestedU nu1 = tagged NestedU1 bu0;
      NestedU nu2 = tagged NestedU2 bs1;
      NestedUP#(8,16,32,Bool,BasicE) nup0 = tagged NestedUP0 be1;
      NestedUP#(8,16,32,Bool,BasicE) nup1 = tagged NestedUP1 bup1;
      NestedUP#(8,16,32,Bool,BasicE) nup2 = tagged NestedUP2 bsp1;
      $display(fshow(nu0));
      $display(fshow(nu1));
      $display(fshow(nu2));
      $display(fshow(nup0));
      $display(fshow(nup1));
      $display(fshow(nup2));

      $display("");

      $display("Nested struct");
      NestedS ns1 =
          NestedS { nestedS0: be0, nestedS1: bu0, nestedS2: bs1 };
      NestedSP#(8,16,32,Bool,BasicE) nsp1 =
          NestedSP { nestedSP0: be1, nestedSP1: bup1, nestedSP2: bsp1 };
      $display(fshow(ns1));
      $display(fshow(nsp1));

      $display("");

      $display("Partially-void union");
      SomeVoidU svu0 = tagged SomeVoidU0;
      SomeVoidU svu1 = tagged SomeVoidU1 False;
      $display(fshow(svu0));
      $display(fshow(svu1));

      $display("");

      $display("Fully-void union");
      AllVoidU avu0 = tagged AllVoidU0;
      AllVoidU avu1 = tagged AllVoidU1;
      $display(fshow(avu0));
      $display(fshow(avu1));

      $display("");

      $display("Empty struct");
      EmptyS es1 = EmptyS { };
      $display(fshow(es1));

      done <= True;
   endrule

   rule doFinish(done);
      $finish(0);
   endrule
   
endmodule
