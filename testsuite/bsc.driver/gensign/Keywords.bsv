
export Sdata(..);

export ParamCstruct(..);
export ParamCtype;
export ParamCdata(..);
export ParamCclass(..);
// These are exported abstractly
export ParamCtypeNotVis;
export ParamCdataNotVis;
export ParamCclassNotVis;
// This export causes ParamCIclass to be exported implicitly
export mkParamCIclass;


// -----

// Test keywords as names of struct fields

typedef struct{

  // bi-file keyword "data"
  Bit#(32) data;

  // "datatype" was an allowed alias for "data", but was not being escaped,
  // which caused a failure to read back in the bi-file
  Bool datatype;

} Sdata deriving(Bits,Eq);


// -----

// Test keywords as parameter names

// Cstruct (interface)
interface ParamCstruct#(type data);
  method Action put(data data);
  method data   get();
endinterface

// Ctype
typedef Reg#(data) ParamCtype#(type data);

// Cdata
typedef union tagged {
   data T1;
   data T2;
} ParamCdata#(type data);

// Cclass
typeclass ParamCclass#(type data);
   function data getParamCclass();
endtypeclass

// Cstruct abstractly exported
// (This doesn't generated CItype, just a Cstruct with the vis field False)
typedef struct {
   data f1;
   data f2;
} ParamCtypeNotVis#(type data);

// Cdata abstractly exported
// (This doesn't generated CItype, just a Cdata with the vis field False)
typedef union tagged {
   data T1;
   data T2;
} ParamCdataNotVis#(type data);

// Cclass abstracly exported
// (This does result in a CIclass)
typeclass ParamCclassNotVis#(type data);
   function data getParamCclassNotVis();
endtypeclass

// CIclass is also created if the class is not exported but is used by
// something which is exported
typeclass ParamCIclass#(type data);
   function data getParamCIclass();
endtypeclass

module mkParamCIclass() provisos(ParamCIclass#(Bool));
endmodule

// CItype would be tested here, but CItype is never generated in a .bi file
// (it's an error for a type to be used but not exported)


// -----

