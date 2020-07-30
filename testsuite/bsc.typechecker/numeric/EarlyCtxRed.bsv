typeclass MyNumAlias#(numeric type a, numeric type b)
   dependencies(a determines b, b determines a);
endtypeclass

instance MyNumAlias#(a,a);
endinstance

// -------------------------

module mkCentralCache ();

    Bit#(16) localData = ?;

    Ifc cache <- mkCacheSetAssoc(?, localData);

endmodule

// -------------------------

interface Ifc;
endinterface

module mkCacheSetAssoc#(Bool srcData, Bit#(n) localData)
        (Ifc)
    provisos ( MyNumAlias#(n, TExp#(TLog#(n))) );

endmodule

// -------------------------
