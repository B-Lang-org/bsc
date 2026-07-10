// A variant of CExtendSynonym that puts a type function (here a user-defined
// ATF, 'IdW') into the id-type synonyms, so that expanding the synonyms in the
// instance head *does* reveal a type function.  That forces the conditional
// synonym expansion in 'CtxRed.ctxRedCQType'' to fire (unlike CExtendSynonym,
// where the plain synonyms are left unexpanded), which re-introduces the
// dangling 'addr_size' parameter and makes typecheck fail with T0035.
//
// This is the case that is *still broken* -- see the XXX in ctxRedCQType' and
// GitHub Issue #311 (and bsc-contrib PR 46, which worked around the analogous
// AMBA_TLM failure by adding explicit method types).  CExtendATFExplicit.bsv
// shows that adding explicit types makes it compile, which suggests the
// problem is one of inference ordering rather than anything fundamental.
// The same failure occurs with the builtin type function SizeOf in place of
// the ATF 'IdW'.

function Bit#(m) zExtend(Bit#(n) value)
   provisos(Add#(n,m,k));
   Bit#(k) out = zeroExtend(value);
   if (valueOf(m) == 0)
      return ?;
   else
      return out[valueOf(m) - 1:0];
endfunction

function a cExtend(b value)
   provisos(Bits#(a, sa), Bits#(b, sb));
   let out = unpack(zExtend(pack(value)));
   return out;
endfunction

// A user-defined ATF: IdW#(Bit#(n)) = n (i.e. it plays the role of SizeOf).
typeclass HasIdW#(type t, numeric type n) dependencies (t determines n);
   type IdW#(type t) = n;
endtypeclass

instance HasIdW#(Bit#(n), n);
endinstance

`define TLM_PRM_DCL numeric type id_size,   \
                    numeric type addr_size

`define TLM_PRM    id_size,   \
                   addr_size

typedef Bit#(IdW#(Bit#(id_size)))  TLMId#(`TLM_PRM_DCL);
typedef Bit#(IdW#(Bit#(id_size)))  AxiId#(`TLM_PRM_DCL);

typedef struct {
                AxiId#(`TLM_PRM)     id;
                } AxiAddrCmd#(`TLM_PRM_DCL);

function TLMId#(`TLM_PRM) fromAxiId(AxiId#(`TLM_PRM) id);
   return cExtend(id);
endfunction

typeclass BusPayload#(type a, type b) dependencies(a determines b);
   function b getId(a payload);
endtypeclass

instance BusPayload#(AxiAddrCmd#(`TLM_PRM), TLMId#(`TLM_PRM));
   function getId(payload);
      return fromAxiId(payload.id);
   endfunction
endinstance
