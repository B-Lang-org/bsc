import Vector::*;
import GetPut::*;
import ClientServer::*;
import PAClib::*;
import Types::*;

//////////////////////////////////////
//       functions for Utilities
//////////////////////////////////////
function Action disp_time(String comment, t a);
   return (action
      $display("%t %s", $time, comment);
   endaction);
endfunction

function Bit#(4) take_4bit(data_t data, UInt#(8) base)
   provisos(Bits#(data_t, data_sz), Add#(4, xxx, data_sz), Bitwise#(data_t));
   data_t data_tmp = data >> (base * 4);
   return truncate(pack(data_tmp));
endfunction


//////////////////////////////////////
//     functions for CountLoop
//////////////////////////////////////
function Tuple2#(CountSumLoop_T, UInt#(5)) mkCountSumLoop_Body(Tuple2#(CountSumLoop_T, UInt#(5)) in);
   match {.countSumLoop_set, .j} = in;
   match {.data, .base, .i, .sum_in} = countSumLoop_set;
   UInt#(5) sum_out = sum_in;
   if (take_4bit(data[j], base) == truncate(pack(i)))
      sum_out = sum_out + 1;
   return tuple2(tuple4(data, base, i, sum_out), j);
endfunction

function UInt#(5) mkCountSumLoop_Final(CountSumLoop_T in) = tpl_4(in);

function CountSumLoop_T mkCountSumLoop_T(CountLoop_T in);
   match {.data, .base, .i} = in;
   return tuple4(data, base, i, 0);
endfunction

function Vector#(16, CountLoop_T) mkVCountLoop_T(Tuple2#(VData_T, UInt#(8)) in);
   match {.data, .base} = in;
   return map(tuple3(data, base), genWith(fromInteger));
endfunction

module [Module] mkCountSumLoop#(PipeOut#(CountLoop_T) in) (PipeOut#(UInt#(5)));

   PipeOut#(CountSumLoop_T) prologue <- mkFn_to_Pipe(mkCountSumLoop_T, in);
   PipeOut#(UInt#(5)) sum <- mkLinearPipe_S_Alt(16, mkFn_to_Pipe(mkCountSumLoop_Body), mkFn_to_Pipe(mkCountSumLoop_Final), prologue);
   return sum;

endmodule

module [Module] mkCountLoop#(PipeOut#(Tuple2#(VData_T, UInt#(8))) in) (PipeOut#(VCount_T));

   PipeOut#(Vector#(16, CountLoop_T)) prologue <- mkFn_to_Pipe(mkVCountLoop_T, in);
   PipeOut#(VCount_T) vcount <- mkMap(mkCountSumLoop, prologue);
   return vcount;

endmodule


//////////////////////////////////////
//     functions for OffsetLoop
//////////////////////////////////////
function OffsetSumLoop_T mkOffsetSumLoop_T(Vector#(15, UInt#(5)) count15);
   return tuple2(count15, 0);
endfunction

function Tuple2#(OffsetSumLoop_T, UInt#(5)) mkOffsetSumLoop_Body(Tuple2#(OffsetSumLoop_T, UInt#(5)) in);
   match {.offsetSumLoop_set, .j} = in;
   match {.count, .sum_in} = offsetSumLoop_set;
   UInt#(5) sum_out = sum_in + count[j];
   return tuple2(tuple2(count, sum_out), j);
endfunction

function UInt#(5) mkOffsetSum_Final(OffsetSumLoop_T in) = tpl_2(in);

// module [Module] mkOffsetSumLoop#(PipeOut#(Vector#(15, UInt#(5))) count15,
//                                  PipeOut#(Vector#(15, UInt#(5))) i
//                                           ) (PipeOut#(UInt#(5)));

//    PipeOut#(OffsetSumLoop_T) prologue <- mkFn_to_Pipe(mkOffsetSumLoop_T, count15);
//    PipeOut#(UInt#(5)) sum <- mkNewLinearPipe_S(i, mkFn_to_Pipe(mkOffsetSumLoop_Body), mkFn_to_Pipe(mkOffsetSum_Final), prologue);
//    return sum;

// endmodule

module [Module] mkOffsetLoop#(PipeOut#(VCount_T) vcount) (PipeOut#(VOffset_T));


   PipeOut#(Vector#(15, UInt#(5))) vcount_15 <- mkFn_to_Pipe(init, vcount);
   let voffset <- mkFn_to_Pipe ( scanl(\+ ,0), vcount_15);
   return voffset;

endmodule


//////////////////////////////////////
//     functions for OutDataLoop
//////////////////////////////////////
function OutDataLoop_T mkOutDataLoop_T(Tuple2#(VData_T, UInt#(8)) inData, VOffset_T voffset);
   match {.data, .base} = inData;
   return tuple4(data, base, voffset, replicate(0));
endfunction

function Tuple2#(OutDataLoop_T, UInt#(5)) mkOutDataLoop_Body(Tuple2#(OutDataLoop_T, UInt#(5)) in);
   match {.set, .i} = in;
   match {.inData, .base, .offset_in, .outData_in} = set;
   let rad = take_4bit(inData[i], base);
   let offset_out = offset_in;
   let outData_out = outData_in;
   outData_out[offset_in[rad]] = inData[i];
   offset_out[rad] = offset_in[rad] + 1;
   return tuple2(tuple4(inData, base, offset_out, outData_out), i);
endfunction

function Tuple2#(VData_T, UInt#(8)) mkOutDataLoop_Final(OutDataLoop_T in);
   match {.inData, .base, .offset, .outData} = in;
   return tuple2(outData, base);
endfunction

module [Module] mkOutDataLoop#(PipeOut#(OutDataLoop_T) in) (PipeOut#(Tuple2#(VData_T, UInt#(8))));

   PipeOut#(Tuple2#(VData_T, UInt#(8))) outData <- mkForLoop(16, mkFn_to_Pipe(mkOutDataLoop_Body), mkFn_to_Pipe(mkOutDataLoop_Final), in);
   return outData;
endmodule

//////////////////////////////////////
//     function for BaseLoop
//////////////////////////////////////
module [Module] mkBaseLoop_Body#(PipeOut#(Tuple2#(VData_T, UInt#(8))) inData) (PipeOut#(Tuple2#(VData_T, UInt#(8))));

   function Tuple2#(a, a) copy_dt(a va) = tuple2(va, va);

   // Prepare two copy of inData for CountLoop and OutDataLoop
   Tuple2#(PipeOut#(Tuple2#(VData_T, UInt#(8))), PipeOut#(Tuple2#(VData_T, UInt#(8)))) fork_Data <- mkFork(copy_dt, inData);
   let inData_1 = tpl_1(fork_Data);
   let inData_2 = tpl_2(fork_Data);

   // CountLoop
   PipeOut#(VCount_T) vcount <- mkCountLoop(inData_1);
   vcount <- mkTap(disp_time("   Finish CountLoop"), vcount);

   // OffsetLoop
   PipeOut#(VOffset_T) voffset <- mkOffsetLoop(vcount);
   voffset <- mkTap(disp_time("   Finish OffsetLoop"), voffset);

   // OutDataLoop
   PipeOut#(OutDataLoop_T) join_Data <- mkJoin(mkOutDataLoop_T, inData_2, voffset);
   PipeOut#(Tuple2#(VData_T, UInt#(8))) outData <- mkOutDataLoop(join_Data);
   outData <- mkTap(disp_time("   Finish OutDataLoop"), outData);

   return outData;

endmodule

module [Module] mkBaseLoop#(PipeOut#(VData_T) inData) (PipeOut#(VData_T));

   PipeOut#(VData_T) baseloop <- mkForLoop(8, mkBaseLoop_Body, mkFn_to_Pipe(id), inData);

   return baseloop;

endmodule


//////////////////////////////////////
//     Top module
//////////////////////////////////////
(* synthesize *)
module mkRadixSort(Server#(VData_T, VData_T));
   let server <- mkPipe_to_Server(mkBaseLoop);
   return server;
endmodule
