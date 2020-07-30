package IFC ;

interface IFC#(type mT);
 method Action start((* port = "sta" *) mT a,(* port = "stb" *) mT b);
 method mT result((* port = "stc" *) mT c);
 method ActionValue#(mT) check((* port = "std" *) mT d);
endinterface

endpackage
