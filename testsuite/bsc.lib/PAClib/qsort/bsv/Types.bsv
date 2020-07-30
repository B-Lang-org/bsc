import Vector::*;

typedef Vector#(num, data_t) VData_T#(numeric type num, type data_t);
typedef UInt#(TLog#(num)) Ptr_T#(numeric type num);

typedef Tuple3#(VData_T#(num, data_t),
                Ptr_T#(num),
                Ptr_T#(num)
) PartitionIn_T#(numeric type num, type data_t);

typedef Tuple5#(VData_T#(num, data_t),   // a[]
                data_t,                  // v
                Ptr_T#(num),             // i
                Ptr_T#(num),             // j
                Ptr_T#(num)              // r
) PartitionLoop_T#(numeric type num, type data_t);

typedef Vector#(num, Ptr_T#(num)) Stack_T#(numeric type num);

typedef Tuple3#(Stack_T#(num), 
                Stack_T#(num),
                Ptr_T#(num)
) MainLoopIn_T#(numeric type num);

typedef Tuple4#(VData_T#(num, data_t),
                Stack_T#(num), 
                Stack_T#(num),
                Ptr_T#(num)
) MainLoopWork_T#(numeric type num, type data_t);

