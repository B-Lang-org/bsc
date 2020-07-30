typedef struct {} Foo#(string type s);

function Action actStringOf(Foo#(s) f);
   return $display(stringOf(s));
endfunction: actStringOf

Foo#("aaa") a = Foo {};

module sysStringOfBSV();
   Foo#("bbb") b = Foo {};

   rule test;
       actStringOf(a);
       actStringOf(b);
       $finish;
   endrule
endmodule
