import FIFO :: *;
typedef enum { Out_0, Out_1 } Dest deriving (Eq,Bits);

interface Switch_IFC #(type t) ;
    method Action put0(Dest destination, t in);
    method Action put1(Dest destination, t in);
    method ActionValue#(t) get0();
    method ActionValue#(t) get1();
endinterface

module switch(Switch_IFC#(int));
   FIFO#(Tuple2#(Dest,int)) inf0<- mkFIFO;
   FIFO#(Tuple2#(Dest,int)) inf1<- mkFIFO;
   FIFO#(int) out0<- mkFIFO;
   FIFO#(int) out1<- mkFIFO;

   rule r0;
      match {.dest, .data} = inf0.first();
      if (dest == Out_0)
        out0.enq(data);
      else
        out1.enq(data);
      inf0.deq();
   endrule

   rule r1;
      match {.dest, .data} = inf1.first();
      if (dest == Out_0)
        out0.enq(data);
      else
        out1.enq(data);
      inf1.deq();
   endrule

   method Action put0(Dest destination, int in);
      inf0.enq(tuple2(destination,in));
   endmethod

   method Action put1(Dest destination, int in);
      inf1.enq(tuple2(destination,in));
   endmethod

   method ActionValue#(int) get0();
     out0.deq();
     return out0.first();
   endmethod

   method ActionValue#(int) get1();
     out1.deq();
     return out1.first();
   endmethod
endmodule
