typedef struct {
    Bool f1;
    Bool f2;
} S deriving (Bits);

// this test requires using the "-g sysNonModule" flag
function S sysNonModule ();
   return (S { f1: True, f2: False });
endfunction

