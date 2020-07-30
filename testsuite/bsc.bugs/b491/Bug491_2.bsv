typedef struct {
  union tagged {
    Bool Left;
    Bool Right;
  } neither;
} NeitherStruct;

function Bool unNeitherStruct(NeitherStruct neitherStruct);
  case (neitherStruct.neither) matches
  tagged Left .b: return b;
  tagged Right .b: return b;
  endcase
endfunction
