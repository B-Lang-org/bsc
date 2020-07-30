package CircPkg;

// Import a package that is pre-compiled with a library called DVIController.
import CircTop::*;

// Define a same interface as in the library, with the same field name,
// but a different type.
interface Ifc;
   method Bit#(1) m();
endinterface

// Now use that field name, causing the typechecker to look it up by type,
// for which it should unexpectedly find two results for the same qualified
// name.
function Ifc make_ifc(Bit#(1) b);
   return (interface Ifc;
              method m = b;
           endinterface);   
endfunction

endpackage
