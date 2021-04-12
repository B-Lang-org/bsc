
(* noinline *)
function bit [31:0] simple_div (bit[31:0] a,bit[31:0] b);
    bit [63:0] top;
    top = zeroExtend (a);
    bit [63:0] bot;
    bot = zeroExtend (b);
    Nat steps = 32;
    bit [31:0] q;
    q = 0;
    while (steps >0)
      begin
        if (top > ((bot) << (steps-1)))
          begin
            top = top - ((bot) << (steps-1));
            q  = q |(1<< steps-1);
          end
        steps = steps -1;
      end
    if (b == 0)
      return(0);
     else
      return(q);
endfunction: simple_div


/*
(* noinline *)
function bit [31:0] simple_mod (bit[31:0] a,bit[31:0] b);
    bit [63:0] top;
    top = zeroExtend(a);
    bit [63:0] bot;
    bot = zeroExtend(b);
    Nat steps = 32;
    bit [31:0] q;
    q = 0;
    while (steps >0)
      begin
        if (top > ((bot) << (steps-1)))
          begin
            top = top - ((bot) << (steps-1));
            q  = q |(1<< steps-1);
          end
        steps = steps -1;
      end
    if (b == 0)
       return(0);
     else
       return(top[31:0]);
endfunction: simple_mod
*/

