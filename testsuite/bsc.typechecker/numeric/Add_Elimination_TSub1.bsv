function Bool fn (Bit#(x) v1, Bit#(y) v2, Bit#(z) v3)
 provisos ( // x greater than y, z
            Add#(y,_1,x),
            Add#(z,_2,x)
          );

   Bit#(TSub#(x,y)) s1 = truncate(v1);
   Bit#(TSub#(x,z)) s2 = truncate(v1);

   Bit#(TAdd#(y,TAdd#(TAdd#(y,z),TAdd#(TSub#(x,y),4)))) n1
       = {v2, {{v2, v3}, {s1, 4'b0}}};
   Bit#(TAdd#(TAdd#(TAdd#(y,TSub#(x,z)),TAdd#(2,z)),TAdd#(2,z))) n2
       = {{{v2, s2}, {2'b0, v3}}, {2'b0, v3}};
   return (n1 == n2);
endfunction
