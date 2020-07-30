function Bit#(4) funcAdd(Bit#(4) a , Bit#(4) b);
Bit#(4) result;
int i;
//result = 4'b0000;
 for (i=0 ; i<4; i=i+1)
  begin
    result[pack(i)] = a[pack(i)] + b[pack(i)];
  end
 return result;
endfunction: funcAdd
