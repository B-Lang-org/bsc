// These types are based on the DeriveFShow example
// and may be overkill for testing deriving of DefaultValue


// Test an isomorphic tagged union
typedef union tagged { Bit#(8) IsoU; } IsoU deriving (DefaultValue, Eq);
// Test a polymorphic version
typedef union tagged { Bit#(n) IsoUP; } IsoUP#(type n) deriving (DefaultValue, Eq);
// Test a fully polymorphic version
typedef union tagged { t IsoUFP; } IsoUFP#(type t) deriving (DefaultValue, Eq);

// Test an isomorhphic struct
typedef struct { Int#(16) isoS; } IsoS deriving (DefaultValue, Eq);
// Test a polymorphic version
typedef struct { Int#(n) isoSP; } IsoSP#(type n) deriving (DefaultValue, Eq);
// Test a fully polymorphic version
typedef struct { t isoSFP; } IsoSFP#(type t) deriving (DefaultValue, Eq);

// Test an enum
typedef enum { Enum0, Enum1, Enum2 } BasicE deriving (DefaultValue, Eq);

// Test a tagged union of basic types
typedef union tagged {
   Bool      BasicU0;
   Bit#(8)   BasicU1;
   UInt#(16) BasicU2;
   Int#(32)  BasicU3;
} BasicU deriving (DefaultValue, Eq);
// Test a polymorphic version
typedef union tagged {
   t1        BasicUP0;
   Bit#(n1)  BasicUP1;
   UInt#(n2) BasicUP2;
   Int#(n3)  BasicUP3;
   t2        BasicUP4;
} BasicUP#(type n1, type n2, type n3, type t1, type t2) deriving (DefaultValue, Eq);

// Test a struct of basic types
typedef struct {
   Bool      basicS0;
   Bit#(8)   basicS1;
   UInt#(16) basicS2;
   Int#(32)  basicS3;
} BasicS deriving (DefaultValue, Eq);
// Test a polymorphic version
typedef struct {
   t1        basicSP0;
   Bit#(n1)  basicSP1;
   UInt#(n2) basicSP2;
   Int#(n3)  basicSP3;
   t2        basicSP4;
} BasicSP#(type n1, type n2, type n3, type t1, type t2) deriving (DefaultValue, Eq);

// Test a tagged union containing enum/union/struct
typedef union tagged {
   BasicE NestedU0;
   BasicU NestedU1;
   BasicS NestedU2;
} NestedU deriving (DefaultValue, Eq);
// Test a polymorphic version
typedef union tagged {
   BasicE                       NestedUP0;
   BasicUP#(n1, n2, n3, t1, t2) NestedUP1;
   BasicSP#(n1, n2, n3, t1, t2) NestedUP2;
} NestedUP#(type n1, type n2, type n3, type t1, type t2) deriving (DefaultValue, Eq);

// Test a struct containing enum/union/struct
typedef struct {
   BasicE nestedS0;
   BasicU nestedS1;
   BasicS nestedS2;
} NestedS deriving (DefaultValue, Eq);
// Test a polymorphic version
typedef struct {
   BasicE                       nestedSP0;
   BasicUP#(n1, n2, n3, t1, t2) nestedSP1;
   BasicSP#(n1, n2, n3, t1, t2) nestedSP2;
} NestedSP#(type n1, type n2, type n3, type t1, type t2) deriving (DefaultValue, Eq);

// Test a tagged union with some void data
typedef union tagged {
   void SomeVoidU0;
   Bool SomeVoidU1;
} SomeVoidU deriving (DefaultValue, Eq);
// Test a tagged union with all void data
// (does it get displayed like an enum?)
typedef union tagged {
   void AllVoidU0;
   void AllVoidU1;
} AllVoidU deriving (DefaultValue, Eq);

// Test a struct with no fields
typedef struct {
} EmptyS deriving (DefaultValue, Eq);


(* synthesize *)
module sysDeriveDefaultValue();

   Reg#(Bool) done <- mkReg(False);

   rule doDisplay(!done);

      $display("Isomorphic tagged union");
      IsoU iu = tagged IsoU 0;
      IsoUP#(16) iup = tagged IsoUP 0;
      IsoUFP#(Int#(32)) iufp = tagged IsoUFP 0;
      if (iu != defaultValue) $display ("FAIL: iu");
      if (iup != defaultValue) $display ("FAIL: iup");
      if (iufp != defaultValue) $display ("FAIL: iufp");

      $display("");

      $display("Isomorphic struct");
      IsoS is = IsoS { isoS: 0 };
      IsoSP#(16) isp = IsoSP { isoSP: 0 };
      IsoSFP#(Int#(32)) isfp = IsoSFP { isoSFP: 0 };
      if (is != defaultValue) $display ("FAIL: is");
      if (isp != defaultValue) $display ("FAIL: isp");
      if (isfp != defaultValue) $display ("FAIL: isfp");

      $display("");

      $display("Basic enum");
      BasicE be = Enum0;
      if (be != defaultValue) $display ("FAIL: be");

      $display("");

      $display("Basic tagged union");
      BasicU bu = tagged BasicU0 False;
      BasicUP#(8,16,32,Bool,BasicE) bup = tagged BasicUP0 False;
      if (bu != defaultValue) $display ("FAIL: bu");
      if (bup != defaultValue) $display ("FAIL: bup");

      $display("");

      $display("Basic struct");
      BasicS bs =
          BasicS { basicS0: False, basicS1: 0, basicS2: 0, basicS3: 0 };
      BasicSP#(8,16,32,Bool,BasicE) bsp =
          BasicSP { basicSP0: False, basicSP1: 0, basicSP2: 0, basicSP3: 0, basicSP4: Enum0 };
      if (bs != defaultValue) $display ("FAIL: bs");
      if (bsp != defaultValue) $display ("FAIL: bsp");

      $display("");

      $display("Nested tagged union");
      NestedU nu = tagged NestedU0 be;
      NestedUP#(8,16,32,Bool,BasicE) nup = tagged NestedUP0 be;
      if (nu != defaultValue) $display ("FAIL: nu");
      if (nup != defaultValue) $display ("FAIL: nup");

      $display("");

      $display("Nested struct");
      NestedS ns =
          NestedS { nestedS0: be, nestedS1: bu, nestedS2: bs };
      NestedSP#(8,16,32,Bool,BasicE) nsp =
          NestedSP { nestedSP0: be, nestedSP1: bup, nestedSP2: bsp };
      if (ns != defaultValue) $display ("FAIL: ns");
      if (nsp != defaultValue) $display ("FAIL: nsp");

      $display("");

      $display("Partially-void union");
      SomeVoidU svu = tagged SomeVoidU0;
      if (svu != defaultValue) $display ("FAIL: svu");

      $display("");

      $display("Fully-void union");
      AllVoidU avu = tagged AllVoidU0;
      if (avu != defaultValue) $display ("FAIL: avu");

      $display("");

      $display("Empty struct");
      EmptyS es = EmptyS { };
      if (es != defaultValue) $display ("FAIL: es");

      done <= True;
   endrule

   rule doFinish(done);
      $finish(0);
   endrule
   
endmodule
