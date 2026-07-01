module DPIWrappers ( genDPIWrappers ) where

import Verilog(VDPI(..), VDPIType(..))
import CCSyntax
import Error(ErrorHandle)
import Flags(Flags(..), quiet)
import FileNameUtil(mkDPICName, getRelativeFilePath, dropSuf)
import FileIOUtil(writeFileCatch)
import PPrint(ppReadable)
import TopUtils(putStrLnF, commentC)

import Control.Monad(unless)
import Data.List(nub)

-- ---------------------------------------------------------------------------
-- DPI wrappers for polymorphic foreign functions
--
-- A monomorphic foreign function needs no wrapper: its DPI-C import names the
-- user's C function directly (mkDPIDeclarations emits no c_identifier alias).
--
-- A polymorphic function is monomorphized into one fixed-width DPI import per
-- concrete width used (see ForeignFunctions.getDPIInstantiations).  Each such
-- import has a mangled SystemVerilog name and links, via a "c_identifier ="
-- alias, to a generated wrapper.  A fixed-width packed operand ("bit [W-1:0]")
-- is passed on the C side as the word-canonical 'svBitVecVal *' for every W,
-- which matches the polymorphic C function's word-pointer ABI, so the wrapper
-- just casts and forwards to the single real C function:
--
--   void poly_add_w7_bs_dpi_wrapper(svBitVecVal* res, const svBitVecVal* a,
--                                   const svBitVecVal* b, unsigned int size) {
--     poly_add((unsigned int*)res, (unsigned int*)a, (unsigned int*)b, size);
--   }
--
-- All wrappers for one function are written to a single "dpi_wrapper_<fn>.c"
-- (so the link step finds them by the function's base name), one wrapper per
-- distinct width used.
-- ---------------------------------------------------------------------------

-- Info for one wrapper: (c_identifier/wrapper name, return type, arg types).
type WrapInfo = (String, VDPIType, [VDPIType])

genDPIWrappers :: ErrorHandle ->
                  Flags -> String -> [String] -> [VDPI] ->
                  IO [CCFragment]
genDPIWrappers errh flags prefix blurb vdpis =
  do -- collect the imports that need a wrapper (those with a c_identifier alias
     -- and an underlying C function), keyed by the real C function name
     let wrapped = [ (cfn, (wname, ret, map thd args))
                   | VDPI _ (Just wname) (Just cfn) ret args <- vdpis ]
         cfns = nub (map fst wrapped)
         groups = [ (cfn, [ wi | (c, wi) <- wrapped, c == cfn ]) | cfn <- cfns ]
     files <- mapM (writeWrapperFile errh flags prefix blurb) groups
     return $ concat files
  where thd (_,_,t) = t

writeWrapperFile :: ErrorHandle -> Flags -> String -> [String] ->
                    (String, [WrapInfo]) -> IO [CCFragment]
writeWrapperFile errh flags prefix blurb (cfn, wraps) =
  do let c_filename = mkDPICName (vdir flags) prefix cfn
         c_filename_rel = getRelativeFilePath c_filename

         -- all wrappers for one function share the underlying C signature;
         -- derive its declaration from the first
         (_, ret0, args0) = head wraps
         real_decl = externC [ mkRealDecl cfn ret0 args0 ]
         wrapper_defs = externC [ define (mkWrapperType wi) (mkWrapperBody cfn wi)
                                | wi <- wraps ]

         c_segments = [ cpp_system_include "svdpi.h"
                      , comment "the underlying polymorphic C function"
                                real_decl
                      , comment "fixed-width DPI wrappers (one per width used)"
                                wrapper_defs
                      ]
         c_contents = commentC blurb ++ ppReadable (program c_segments)

     writeFileCatch errh c_filename c_contents
     unless (quiet flags) $ putStrLnF $ "DPI wrapper file created: " ++
                                        (dropSuf c_filename_rel) ++ ".c"
     return c_segments

-- The prototype of the underlying (real) C function, whose ABI passes wide and
-- polymorphic values as 'unsigned int *' and scalars by value.
mkRealDecl :: String -> VDPIType -> [VDPIType] -> CCFragment
mkRealDecl cfn ret args =
  decl $ function (retCType ret) (mkVar cfn)
                  [ decl $ (realCType t) (mkVar "") | t <- args ]

mkWrapperType :: WrapInfo -> CCFragment
mkWrapperType (wname, rett, args) =
  function (retCType rett) (mkVar wname)
           [ decl $ (dpiCType t) (mkVar (argName i)) | (i,t) <- zip [(0::Int)..] args ]

mkWrapperBody :: String -> WrapInfo -> CCFragment
mkWrapperBody cfn (_, rett, args) =
  let call = (var cfn) `cCall` [ fwd t (argName i) | (i,t) <- zip [(0::Int)..] args ]
  in block [ if rett == VDT_void then stmt call else ret (Just call) ]

argName :: Int -> String
argName i = "a" ++ show i

-- The C type of an operand as seen by the wrapper (the DPI ABI): fixed-width
-- packed operands are 'svBitVecVal *'; scalars are by value.
dpiCType :: VDPIType -> (CCFragment -> CCFragment)
dpiCType VDT_void       = void
dpiCType VDT_byte       = unsigned . char
dpiCType VDT_int        = unsigned . int
dpiCType VDT_longint    = unsigned . long . long
dpiCType (VDT_wide _)   = ptr . userType "svBitVecVal"
dpiCType VDT_string     = ptr . char
dpiCType VDT_poly       = ptr . userType "svBitVecVal"

-- The C type of an operand as seen by the real function.
realCType :: VDPIType -> (CCFragment -> CCFragment)
realCType VDT_void      = void
realCType VDT_byte      = unsigned . char
realCType VDT_int       = unsigned . int
realCType VDT_longint   = unsigned . long . long
realCType (VDT_wide _)  = ptr . unsigned . int
realCType VDT_string    = ptr . char
realCType VDT_poly      = ptr . unsigned . int

-- The C type of the return value (scalars; wide/poly returns go via an output
-- argument, so the actual return is void in that case).
retCType :: VDPIType -> (CCFragment -> CCFragment)
retCType = realCType

-- Forward a wrapper operand to the real C function, casting packed operands
-- from svBitVecVal* to unsigned int* and strings to char*.
fwd :: VDPIType -> String -> CCExpr
fwd (VDT_wide _) nm = cCast (ptrType (classType "unsigned int")) (var nm)
fwd VDT_poly     nm = cCast (ptrType (classType "unsigned int")) (var nm)
fwd VDT_string   nm = cCast (ptrType (classType "char")) (var nm)
fwd _            nm = var nm
