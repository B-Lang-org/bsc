import MyGetPut::*;

interface MyClient#(type a, type b);
   interface MyGet#(a) request;
   interface MyPut#(b) response;
endinterface

interface MyServer#(type a, type b);
   interface MyPut#(a) request;
   interface MyGet#(b) response;
endinterface



