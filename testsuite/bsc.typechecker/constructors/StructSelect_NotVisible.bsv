import StructSelect_NotVisible_Sub::*;

function Bool fn1();
  MyT1 x = mkT1;
  // test with the right name
  return x.field1;
endfunction

function Bool fn2();
  MyT1 x = mkT1;
  // test with the wrong name
  return x.foobar;
endfunction

function Bool fn3();
  MyT2 x = mkT2;
  // any name is wrong, but try one that exists
  return x.field1;
endfunction

function Bool fn4();
  MyT2 x = mkT2;
  // try one that (hopefully) doesn't exist
  return x.foobarbaz;
endfunction

