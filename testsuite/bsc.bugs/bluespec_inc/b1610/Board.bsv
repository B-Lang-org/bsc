
import Vector::*;

// -------------------------

typedef 2 PERows;

(* synthesize *)
module mkLifeBoard();

  Vector#(PERows,LifePE) left_pes = cons(?,?);
  LifeMesh#(PERows,1) left_boundary <- toMeshV(left_pes);

endmodule: mkLifeBoard

// -------------------------

interface LifePE;
endinterface

interface LifeMesh#(numeric type r, numeric type c);
endinterface

// -------------------------

typeclass ToMeshV#(type t, numeric type r, numeric type c)
   dependencies (t determines (r,c));
   module toMeshV(t x, LifeMesh#(r,c) ifc);
endtypeclass

instance ToMeshV#(LifePE,1,1);
   module toMeshV(LifePE pe, LifeMesh#(1,1) ifc);
      return ?;
   endmodule
endinstance

instance ToMeshV#(Vector#(1,t),r,c)
   provisos(ToMeshV#(t,r,c));

   module toMeshV(Vector#(1,t) vec, LifeMesh#(r,c) ifc);
      let _m <- toMeshV(vec[0]);
      return _m;
   endmodule
endinstance

instance ToMeshV#(Vector#(m,t),r_times_m,c)
   provisos( ToMeshV#(t,r,c), Mul#(r,m,r_times_m), Add#(1,m_minus_1,m), Add#(2,m_minus_2,m)
           , Add#(r,r_times__m_minus_1,r_times_m)
	   , ToMeshV#(Vector#(m_minus_1,t),r_times__m_minus_1,c)
	   // I shouldn't need to state any of this
	   , Add#(1,c_minus_1,c)
	   , Add#(r,c_minus_1,TSub#(TAdd#(r,c),1))
	   , Add#(c_minus_1,r_times__m_minus_1,TSub#(TAdd#(r_times__m_minus_1,c),1))
	   , Add#(TSub#(TAdd#(r,c),1),r_times__m_minus_1,TSub#(TAdd#(r_times_m,c),1))
	   , Add#(TSub#(TAdd#(r_times__m_minus_1,c),1),r,TSub#(TAdd#(r_times_m,c),1))
           );

   module toMeshV(Vector#(m,t) vec, LifeMesh#(r_times_m,c) ifc);
      LifeMesh#(r,c) top_mesh <- toMeshV(head(vec));
      LifeMesh#(r_times__m_minus_1,c) bottom_mesh <- toMeshV(tail(vec));
      return ?;
   endmodule
endinstance

// -------------------------

