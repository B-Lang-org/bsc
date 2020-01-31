package TieOff ;

import Vector::*;

// TieOff package
// This package provides a typeclass TieOff#(t)
// which can be useful to enable methods of some interface t, which must
// be always_enabled or require some action.

// Example -- a tieoff for a Get interface.
// This is "sink" function which pulls the data from the get interface
// and displays the data.
//
// instance TieOff #(Get #(t) )
//    provisos( Bits#(t,st) );
//    module mkTieOff ( Get#(t) ifc, Empty inf);
//       rule getSink (True);
//          t val <- ifc.get;
//          $display("Value from get interface is: %h", val);
//       endrule
//    endmodule
// endinstance



typeclass TieOff #(type t);
  module mkTieOff#(t ifc) (Empty);
endtypeclass

instance TieOff #( Vector#(n,t) )
   provisos (TieOff#(t));
   module mkTieOff#(Vector#(n,t) ifc) (Empty);
      mapM(mkTieOff, ifc);
   endmodule
endinstance



endpackage
