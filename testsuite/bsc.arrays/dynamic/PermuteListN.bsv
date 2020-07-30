import ListN::*;

typedef 64 N;
typedef TLog#(N) K;

function ListN#(n, a) permute_out(ListN#(n, UInt#(k)) indices, ListN#(n, a) vals) provisos(Log#(n, k));
    ListN#(n, a) result = ?;
    let n = fromInteger(valueOf(n));

    for(Integer i = 0; i < n; i = i + 1)
      result[indices[i]] = vals[i];
  
    return(result);
endfunction

(* noinline *) 
function ListN#(N, Bit#(16)) permute_out_N_16(ListN#(N, UInt#(K)) indices, ListN#(N, Bit#(16)) vals) = permute_out(indices, vals);

(* noinline *) 
function ListN#(N, Bit#(16)) permute_in_N_16(ListN#(N, UInt#(K)) indices, ListN#(N, Bit#(16)) vals) = permute_in(indices, vals);

function ListN#(n, a) permute_in(ListN#(n, UInt#(k)) indices, ListN#(n, a) vals) provisos(Log#(n, k));
    ListN#(n, a) result = ?;
    let n = fromInteger(valueOf(n));

    for(Integer i = 0; i < n; i = i + 1)
      result[i] = vals[indices[i]];
  
    return(result);
endfunction
