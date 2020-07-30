interface IFC#(type t);
   method t get();
endinterface

/*
// Parser does not yet accept modules in typeclass declarations
typeclass MyConnect#(type t);
    module mkConnect#(parameter t val) (IFC#(t));
endtypeclass
*/

// So we define it in Classic
(* bluespec_classic_def="\
class MyConnect a where {\n\
    mkConnect :: (IsModule m c) => a -> m (IFC a) }\
" *)

instance MyConnect#(Bool);
   module mkConnect#(parameter Bool val) (IFC#(Bool));
      method get = val;
   endmodule
endinstance

