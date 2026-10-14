package IncoherentUse;

import Helper::*;
import BoolDescribable::*;
import GeneralDescribable::*;

// applyDescribe carries the Describable#(a) constraint explicitly.
function String applyDescribe(a x) provisos(Describable#(a));
    return describe(x);
endfunction

// testFn has Bits#(a,aw) but NOT Describable#(a) in its provisos.
// Calling applyDescribe(x) generates the predicate Describable#(a), which is
// not a given, so instance resolution fires against the imported instances:
//   BoolDescribable's Describable#(Bool) fails one-way matchTop for rigid 'a'
//   but predUnify succeeds, setting incoherent=True.
//   GeneralDescribable's Describable#(a) matches with incoherent=True.
// Without -incoherent-instance-matches: bad_match -> T0030 compile error.
// With    -incoherent-instance-matches: commits via GeneralDescribable
//   (recordPackageUse fires) + T0126 warning.  No T0157 for GeneralDescribable.
function String testFn(a x) provisos(Bits#(a, aw));
    return applyDescribe(x);
endfunction

endpackage
