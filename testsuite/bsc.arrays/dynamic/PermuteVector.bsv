import Vector::*;

typedef 64 N;
typedef TLog#(N) K;

function Vector#(n, a) permute_out(Vector#(n, UInt#(k)) indices, Vector#(n, a) vals) provisos(Log#(n, k));
    Vector#(n, a) result = ?;
    let n = fromInteger(valueOf(n));

    for(Integer i = 0; i < n; i = i + 1)
      result[indices[i]] = vals[i];
  
    return(result);
endfunction

(* noinline *) 
function Vector#(N, Bit#(16)) permute_out_N_16(Vector#(N, UInt#(K)) indices, Vector#(N, Bit#(16)) vals) = permute_out(indices, vals);

(* noinline *) 
function Vector#(N, Bit#(16)) permute_in_N_16(Vector#(N, UInt#(K)) indices, Vector#(N, Bit#(16)) vals) = permute_in(indices, vals);

function Vector#(n, a) permute_in(Vector#(n, UInt#(k)) indices, Vector#(n, a) vals) provisos(Log#(n, k));
    Vector#(n, a) result = ?;
    let n = fromInteger(valueOf(n));

    for(Integer i = 0; i < n; i = i + 1)
      result[i] = vals[indices[i]];
  
    return(result);
endfunction
