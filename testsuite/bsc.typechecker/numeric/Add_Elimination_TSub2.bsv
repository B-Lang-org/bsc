function Bool fn (Bit#(x) v1, Bit#(y) v2, Bit#(z) v3)
 provisos ( // x greater than z
            Add#(z,_2,x)
          );

   Bit#(TAdd#(y,TAdd#(TSub#(x,z),4))) n1
       = {v2, {truncate(v1), 4'b0}};
   Bit#(TSub#(TAdd#(2,TAdd#(TAdd#(x,y),2)),z)) n2
       = truncate({2'b0, {{v1, v2}, 2'b0}});
   return (n1 == n2);
endfunction
