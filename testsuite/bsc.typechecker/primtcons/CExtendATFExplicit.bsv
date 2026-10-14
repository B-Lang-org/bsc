// As CExtendATF.bsv, but with an explicit type on the 'getId' method.  With
// the explicit type, typecheck succeeds despite the ATF-triggered synonym
// expansion in the instance head.  This is the workaround used in bsc-contrib
// PR 46, and it shows that the CExtendATF failure is not fundamental (see the
// XXX in CtxRed.ctxRedCQType' and GitHub Issue #311).

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
   function TLMId#(`TLM_PRM) getId(AxiAddrCmd#(`TLM_PRM) payload);
      return fromAxiId(payload.id);
   endfunction
endinstance
