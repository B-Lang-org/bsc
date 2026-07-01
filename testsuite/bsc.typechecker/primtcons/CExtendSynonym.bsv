// Reduced version of the bsc-contrib AMBA_TLM library (see bsc-contrib PR 46).
// Check that we can use type synonyms in instance heads.  The synonyms 'TLMId'
// and 'AxiId' drop the 'addr_size' parameter; expanding them fully in the
// instance head would leave 'addr_size' dangling and break unification.  This
// exercises the (now conditional) synonym expansion in CtxRed.ctxRedCQType' --
// see the XXX there and GitHub Issue #311.  Because these synonyms contain no
// type function, the conditional expansion leaves them alone, so this compiles;
// bsc-contrib PR 46 added explicit method types to work around the earlier
// (unconditional-expansion) failure, and those are no longer needed here.
// CExtendATF.bsv shows a variant that *does* still fail, because it puts a type
// function in the synonyms and so triggers the expansion.

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

`define TLM_PRM_DCL numeric type id_size,   \
                    numeric type addr_size

`define TLM_PRM    id_size,   \
                   addr_size

typedef Bit#(id_size)     TLMId#(`TLM_PRM_DCL);
typedef Bit#(id_size)     AxiId#(`TLM_PRM_DCL);

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
