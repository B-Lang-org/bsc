typedef Bit#(64) DWord;

typedef struct {
   DWord quo;
   DWord rem;
} DivResult deriving (Bits, Eq);

(* noinline *)
function /*Tuple2#(DWord, DWord)*/ DivResult divide(DWord x, DWord d, Bool sign);

    DWord q = 0;                              
    DWord p = 0;
    Bool xSign = False;
    Bool dSign = False;

    if (sign) begin
        if (x[63]==1) begin
            xSign = True;
            x = -x;
        end
        if (d[63]==1) begin
            dSign = True;
            d = -d;
        end
    end

    p = x >> 63;
    for(Integer i = 63; i > 0; i=i-1) begin
        x = x << 1;
        if (d > p)
            p = (p << 1) + (x >> 63);
        else begin
            p = ((p - d) << 1) + (x >> 63);
            q[i] = 1;
        end
    end

    if (d <= p) begin
        p = p - d;
        q[0] = 1;
    end

    if (xSign) begin
        p = -p;
        if (!dSign)
            q = -q;
    end
    if (!xSign && dSign)
        q = -q;

    //return tuple2(q,p);
    return DivResult{quo:x, rem:d};
endfunction				      
