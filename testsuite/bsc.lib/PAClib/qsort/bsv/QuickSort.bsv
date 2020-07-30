import Vector::*;
import GetPut::*;
import ClientServer::*;
import CompletionBuffer::*;
import PAClib::*;
import Types::*;
import MyPAClib::*;

/////////////////////////////////////////////////////
//  functions/modules for partition                //
/////////////////////////////////////////////////////
function PartitionLoop_T#(num, data_t) partition_prologue(PartitionIn_T#(num, data_t) in);
   match {.va, .l, .r} = in;
   return tuple5(va, va[r], l-1, r, r);
endfunction

module [Module] mkPartitionLoop_preTest#(PipeOut#(PartitionLoop_T#(num, data_t)) in) (PipeOut#(Tuple2#(PartitionLoop_T#(num, data_t), Bool)))

   provisos(Bits#(data_t, data_sz), Ord#(data_t));

   Reg#(Bool) running <- mkReg(False);
   Reg#(Bool) left_finish <- mkReg(False);
   Reg#(Bool) right_finish <- mkReg(False);
   Reg#(VData_T#(num, data_t)) va <- mkRegU;
   Reg#(data_t) v <- mkRegU;
   Reg#(Ptr_T#(num)) i <- mkRegU;
   Reg#(Ptr_T#(num)) j <- mkRegU;
   Reg#(Ptr_T#(num)) r <- mkRegU;

   Bool deq_ok = (running && left_finish && right_finish);

   rule get_input(!running);
      match {.va_in, .v_in, .i_in, .j_in, .r_in} = in.first;
      va <= va_in;
      v <= v_in;
      i <= i_in + 1;
      j <= j_in - 1;
      r <= r_in;
      in.deq;
      running <= True;
      left_finish <= False;
      right_finish <= False;
   endrule

   rule increment_left_ptr(running && !left_finish);
      if (va[i] < v) i <= i + 1;
      else left_finish <= True;
   endrule

   rule decrement_right_ptr(running && !right_finish);
      if (va[j] > v) j <= j - 1;
      else right_finish <= True;
   endrule

   return (interface PipeOut;
      method Tuple2#(PartitionLoop_T#(num, data_t), Bool) first if (deq_ok);
         return tuple2(tuple5(va, v, i, j, r), !(i >= j)); 
      endmethod
      method Action deq if (deq_ok);
         running <= False;
      endmethod
      method Bool notEmpty;
         return deq_ok;
      endmethod
   endinterface);
endmodule

function PartitionLoop_T#(num, data_t) partitionLoop_postTest(PartitionLoop_T#(num, data_t) in);
   match {.va, .v, .i, .j, .r} = in;
   let t = va[i];
   va[i] = va[j];
   va[j] = t;
   return tuple5(va, v, i, j, r);
endfunction

function Tuple2#(VData_T#(num, data_t), Ptr_T#(num)) partitionLoop_final(PartitionLoop_T#(num, data_t) in);
   match {.va, .v, .i, .j, .r} = in;
   let t = va[i];
   va[i] = va[r];
   va[r] = t;
   return tuple2(va, i);
endfunction

module [Module] mkPartition#(PipeOut#(PartitionIn_T#(num, data_t)) in) (PipeOut#(Tuple2#(VData_T#(num, data_t), Ptr_T#(num))))

   provisos (Bits#(data_t, data_sz), Ord#(data_t));

   PipeOut#(PartitionLoop_T#(num, data_t)) prologue <- mkFn_to_Pipe(partition_prologue, in);
   PipeOut#(Tuple2#(VData_T#(num, data_t), Ptr_T#(num))) result <- mkWhileLoop(
           mkPartitionLoop_preTest,
           mkFn_to_Pipe(partitionLoop_postTest),
           mkFn_to_Pipe(partitionLoop_final),
           prologue);
   return result;
endmodule

function Tuple2#(PartitionIn_T#(num, data_t), Tuple2#(CBToken#(8), MainLoopIn_T#(num))) preapre_data(Tuple2#(CBToken#(8), MainLoopWork_T#(num, data_t)) in);
   match {.token, .set} = in;
   match {.va, .leftstack, .rightstack, .sp} = set;
   let t1 = tuple3(va, leftstack[sp], rightstack[sp]);
   let t2 = tuple3(leftstack, rightstack, sp);
   return tuple2(t1, tuple2(token, t2));
endfunction

function Tuple2#(CBToken#(8), MainLoopWork_T#(num, data_t)) update_stack(Tuple2#(VData_T#(num, data_t), Ptr_T#(num)) x1, Tuple2#(CBToken#(8), MainLoopIn_T#(num)) x2);
   match {.va, .v} = x1;
   match {.token, .set} = x2;
   match {.leftstack, .rightstack, .sp} = set;
   let l = leftstack[sp];
   let r = rightstack[sp];
   if (v - l < r - v) begin
      leftstack[sp] = v + 1;
      rightstack[sp] = r;
      sp = sp + 1;
      leftstack[sp] = l;
      rightstack[sp] = v - 1;
      sp = sp + 1;
   end
   else begin
      leftstack[sp] = l;
      rightstack[sp] = v - 1;
      sp = sp + 1;
      leftstack[sp] = v + 1;
      rightstack[sp] = r;
      sp = sp + 1;
   end
   return tuple2(token, tuple4(va, leftstack, rightstack, sp));
endfunction

module [Module] mkTruePath#(PipeOut#(Tuple2#(CBToken#(8), MainLoopWork_T#(num, data_t))) in) (PipeOut#(Tuple2#(CBToken#(8), MainLoopWork_T#(num, data_t))))

   provisos (Bits#(data_t, data_sz), Ord#(data_t));

   Tuple2#(PipeOut#(PartitionIn_T#(num, data_t)), PipeOut#(Tuple2#(CBToken#(8), MainLoopIn_T#(num)))) fork_data <- mkFork(preapre_data, in);
   let dt_for_partition = tpl_1(fork_data);
   let dt_for_update_stack = tpl_2(fork_data);
   PipeOut#(Tuple2#(VData_T#(num, data_t), Ptr_T#(num))) partition <- mkPartition(dt_for_partition);
   PipeOut#(Tuple2#(CBToken#(8), MainLoopWork_T#(num, data_t))) result <- mkJoin(update_stack, partition, dt_for_update_stack);
   return result;
endmodule

function Tuple2#(MainLoopWork_T#(num, data_t), Bool) decrement_sp(MainLoopWork_T#(num, data_t) in);
   match {.va, .leftstack, .rightstack, .sp} = in;
   sp = sp - 1;
   return tuple2(tuple4(va, leftstack, rightstack, sp), leftstack[sp] < rightstack[sp]);
endfunction

function Tuple2#(MainLoopWork_T#(num, data_t), Bool) mainLoop_preTest (MainLoopWork_T#(num, data_t) in);
   return tuple2(in, tpl_4(in) != 0);
endfunction

module [Module] mkMainLoop_postTest#(PipeOut#(MainLoopWork_T#(num, data_t)) in) (PipeOut#(MainLoopWork_T#(num, data_t)))

   provisos (Bits#(data_t, data_sz), Ord#(data_t));

   PipeOut#(Tuple2#(MainLoopWork_T#(num, data_t), Bool)) prologue <- mkFn_to_Pipe(decrement_sp, in);
   PipeOut#(MainLoopWork_T#(num, data_t)) result <- mkIfThenElse_ordered(mkTruePath, mkFn_to_Pipe(id), prologue);
   return result;

endmodule

function VData_T#(num, data_t) mainLoop_final(MainLoopWork_T#(num, data_t) in);
   return tpl_1(in);
endfunction

function MainLoopWork_T#(num, data_t) make_MainLoopWork_T(VData_T#(num, data_t) va, MainLoopIn_T#(num) x);
   match {.leftstack, .rightstack, .sp} = x;
   return tuple4(va, leftstack, rightstack, sp);
endfunction

module [Module] mkQuickSortPipe#(PipeOut#(VData_T#(num, data_t)) inData) (PipeOut#(VData_T#(num, data_t)))

   provisos (Bits#(data_t, data_sz), Ord#(data_t));

   PipeOut#(MainLoopIn_T#(num)) init_value <- mkSource_from_constant(tuple3(replicate(0), replicate(fromInteger(valueOf(num)-1)), 1));
   PipeOut#(MainLoopWork_T#(num, data_t)) joinData <- mkJoin(make_MainLoopWork_T, inData, init_value);
   PipeOut#(VData_T#(num, data_t)) result <- mkWhileLoop(mkFn_to_Pipe(mainLoop_preTest), mkMainLoop_postTest, mkFn_to_Pipe(mainLoop_final), joinData);
   return result;

endmodule


(* synthesize *)
module mkQuickSort(Server#(VData_T#(16, Bit#(32)), VData_T#(16, Bit#(32))));
   let server <- mkPipe_to_Server(mkQuickSortPipe);
   return server;
endmodule

