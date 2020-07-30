import IfcPragmaQualLookup_Sub::*;

interface Ifc;
  // this method is the same as one in the imported package,
  // except that we attach rename attributes
  //
  (* enable="EN_newname" *)
  (* ready="RDY_newname" *)
  method Action oldname();

  // this method does not appear in the imported package;
  // if the module has ports for this method, that confirms that the
  // correct interface is being used (so if the other port is not
  // renamed, it's not because the wrong interface is being used)
  //
  method Action m2();
endinterface

(* synthesize *)
module sysIfcPragmaQualLookup (Ifc);
endmodule

