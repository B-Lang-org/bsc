// clocked_by etc. in tuple(...) are handled exactly as in tuple2(...):
// the tuple is not a module, so this is T0107 for both

module mkM();
   Clock c <- exposeCurrentClock;
   let t = tuple(True, False, clocked_by c);
endmodule
