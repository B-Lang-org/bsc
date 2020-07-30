export MyT1, MyT2;
export mkT1, mkT2;

typedef struct {
  Bool field1;
  Bit#(8) field2;
} MyT1 deriving (Eq, Bits);

typedef union tagged {
  Bool Tag1;
  Bit#(8) Tag2;
} MyT2 deriving (Eq, Bits);

function MyT1 mkT1();
  return (MyT1 { field1: True, field2: 0 });
endfunction

function MyT2 mkT2();
  return (tagged Tag2 0);
endfunction

