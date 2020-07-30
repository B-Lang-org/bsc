
import Vector :: *;

typedef Vector#(rows, Vector#(cols, atype)) 
        Matrix#(type rows, type cols, type atype) ;

function Matrix#(row,col,a_type) mtrxReplicate( a_type val ) ;
   return Vector::replicate( (Vector::replicate(val) ) ) ;
endfunction

function m#(Matrix#(row,col,a_type)) mtrxReplicateM( m#(a_type) mfunc )
   provisos ( Monad#(m) ) ;
   return Vector::replicateM( (Vector::replicateM(mfunc) ) ) ;
endfunction

module mkTest (Empty);
   // accidentally use non-monadix replicate
   Matrix#(5, 5, Reg#(Bool)) mtxOfreg
       // <- mtrxReplicateM(mkReg(True));
       <- mtrxReplicate(mkReg(True));
endmodule
