
import ReExportPkgBSV_Q::*;

T x = 3;

// This should compile (tests "T2" type, "T2" constructor, and value "v")
T2 y = T2(v);

// This should compile
// (And tests that instances are exported too)
T z = 2 + x;

