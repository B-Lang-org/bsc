
// type synonym which needs to be expanded
typedef Bit#(dsz) Data#(numeric type asz, numeric type dsz);

interface Rx#(numeric type asz, numeric type dsz);
   method    Action           putdata (Data#(asz, dsz) x);
endinterface

interface Tx#(numeric type asz, numeric type dsz);
   method    Data#(asz, dsz)  getdata ();
endinterface

typeclass Connectable#(type a, type b);
   module mkConnection#(a x1, b x2)(Empty);
endtypeclass

instance Connectable#(Tx#(b, c), Rx#(f, c))
   provisos (Add#(f, 1, b));
   module mkConnection#(Tx#(b, c) tx,
                        Rx#(f, c) rx) (Empty);
      rule connect;
         rx.putdata(tx.getdata);
      endrule
   endmodule
endinstance

