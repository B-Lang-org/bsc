import ListN::*;
import Connectable::*;

typeclass IVec#(type n, type a, type t)
          dependencies (t determines (n, a), (n, a) determines t);
    function t toIVec(ListN#(n,a) v);
    function ListN#(n,a) fromIVec(t x);
endtypeclass

instance Connectable#(ivat, ivbt)
   provisos (Connectable#(a,b), IVec#(n,a,ivat), IVec#(n,b,ivbt));
   module mkConnection#(ivat iva, ivbt ivb)(Empty);
      mkConnection(fromIVec(iva), fromIVec(ivb));
   endmodule
endinstance