package ReExportSame_TopBad;

import ReExportSame_Sub::*;

export ReExportSame_Sub::*;
export T(..);

// define our own local copy
typedef union tagged {
  Bool Tag1;
  Bool Tag2;
 } T;

endpackage

