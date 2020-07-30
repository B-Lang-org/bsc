import Vector::*;

typedef Vector#(16, Bit#(32)) VData_T;
typedef Vector#(16, UInt#(5)) VCount_T;
typedef VCount_T              VOffset_T;

typedef Tuple3#(VData_T,    // inData[]
                UInt#(8),   // base
                UInt#(5)    // i
) CountLoop_T;

typedef Tuple4#(VData_T,    // inData[]
                UInt#(8),   // base
                UInt#(5),   // i
                UInt#(5)    // sum
) CountSumLoop_T;

typedef Tuple2#(Vector#(15, UInt#(5)), // count15[]
                UInt#(5)               // sum
) OffsetSumLoop_T;

typedef Tuple4#(VData_T,    // inData[]
                UInt#(8),   // base
                VOffset_T,  // offset[]
                VData_T     // outData[]
) OutDataLoop_T;

