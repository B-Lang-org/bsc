interface MyGet#(type a);
   method ActionValue#(a) get();
endinterface

interface MyPut#(type a);
   method Action put(a val);
endinterface

