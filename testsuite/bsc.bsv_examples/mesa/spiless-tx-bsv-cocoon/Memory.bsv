import RegFile::*;
interface Memory#(type addrt, type datat);
   method Action write(addrt addr, datat data);
   method datat read(addrt addr);
endinterface: Memory

module mkMemory(Memory#(addrt, datat))
   provisos(Bounded#(addrt), Bits#(addrt, as), Bits#(datat, ad));
   
   RegFile#(addrt, datat) arr();
   mkRegFileFull the_arr(arr);

   method write = arr.upd; 
   method read = arr.sub;
endmodule: mkMemory

module mkMemoryLoad#(String f, addrt l, addrt h) (Memory#(addrt, datat))
   provisos(Bounded#(addrt), Bits#(addrt, as), Bits#(datat, ad));
   
   RegFile#(addrt, datat) arr();
   mkRegFileLoad#(f,l,h) the_arr(arr);

   method write = arr.upd; 
   method read = arr.sub;
endmodule: mkMemoryLoad
