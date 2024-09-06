{-# LANGUAGE CPP #-}
module CSyntax(
        CPackage(..),
        CSignature(..),
        CExpr(..),
        CCaseArm(..),
        CCaseArms,
        CType,
        TyVar(..),
        TyCon(..),
        Kind(..),
        PartialKind(..),
        CImport(..),
        CInclude(..),
        CQual(..),
        CClause(..),
        CPat(..),
        Literal(..),
        Type(..),
        TISort(..),
        CQType(..),
        CDef(..),
        CExport(..),
        CRule(..),
        CDefn(..),
        CDefl(..),
        CFunDeps,
        CPred(..),
        CTypeclass(..),
        CField(..),
        CFields,
        CStmt(..),
        CStmts,
        IdK(..),
        CLiteral(..),
        CMStmt(..),
        COp(..),
        CPOp(..),
        CFixity(..),
        RulePragma(..),
        xWrapperModuleVerilog,
        xClassicModuleVerilog,
        CInternalSummand(..), CSummands, getCISName,
        COriginalSummand(..), COSummands, getCOSName,
        cApply,
        cmtApply,
        cTApplys,
        cTCon,
        cTVar,
        leftCon,
        anyExpr,
        anyExprAt,
        anyTExpr,
        noType,
        cTApply,
        iKName,
        impName,
        cVar,
        cVApply,
        getName,
        getLName,
        getDName,
        isTDef,
        getNK,
        isCQFilter,
        HasPosition(..),
        StructSubType(..)) where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import Data.Char(isAlpha)
import Data.List(intercalate, genericReplicate)
import Eval
import Lex(isIdChar)
import PPrint
import ErrorUtil
import Position
import Id
import IdPrint
import Literal
import IntegerUtil(integerFormat)
import Undefined
import PreIds
import CType
import VModInfo
import Type(tClock, tReset)
import Pragma
import Util(itos, log2, fromJustOrErr)
import Data.Maybe(listToMaybe)
import Data.List(genericLength)
import FStringCompat
import PreStrings(fsEmpty)

-- Complete package
data CPackage = CPackage
                Id                -- package name
                (Either [CExport]
                        [CExport]) -- export identifiers
                                  -- Left exps = export only exps
                                  -- Right exps = export everything but exps
                [CImport]         -- imported identifiers
                [CFixity]         -- fixity declarations for infix operators
                [CDefn]                  -- top level definitions
                [CInclude]        -- any `include files
        deriving (Eq, Ord, Show)

data CExport
        = CExpVar Id    -- export a variable identifier
        | CExpCon Id    -- export a constructor
        | CExpConAll Id -- export an identifier and constructors
                        -- (datatypes, interfaces, etc.)
        | CExpPkg Id    -- export an entire package
        deriving (Eq, Ord, Show)

data CImport
        = CImpId Bool Id                                -- Bool indicates qualified
        | CImpSign String Bool CSignature
        deriving (Eq, Ord, Show)

-- Package signature from import
data CSignature
        = CSignature Id [Id] [CFixity] [CDefn]        -- package name, imported packages, definitions
        deriving (Eq, Ord, Show)

data CFixity
        = CInfix  Integer Id
        | CInfixl Integer Id
        | CInfixr Integer Id
        deriving (Eq, Ord, Show)

-- Top level definition
data CDefn
        = Ctype IdK [Id] CType
        | Cdata { cd_visible :: Bool,
                  cd_name :: IdK,
                  cd_type_vars :: [Id],
                  cd_original_summands :: COSummands,
                  cd_internal_summands :: CSummands,
                  cd_derivings :: [CTypeclass] }
        | Cstruct Bool StructSubType IdK [Id] CFields
                  [CTypeclass]
                  -- Bool indicates the constrs are visible
                  -- first [Id] are the names of this definition's argument type variables
                  -- last [CTypeclass] are derived classes
        -- incoherent_matches superclasses name_with_kind variables fundeps default_methods
        | Cclass (Maybe Bool) [CPred] IdK [Id] CFunDeps CFields
        | Cinstance CQType [CDefl]
        | CValue Id [CClause]
        | CValueSign CDef
        | Cforeign { cforg_name :: Id,
                     cforg_type :: CQType,
                     cforg_foreign_name :: Maybe String,
                     cforg_ports :: Maybe ([String], [String]),
                     cforg_is_noinline :: Bool }
        | Cprimitive Id CQType
        | CprimType IdK
        | CPragma Pragma
        -- only in package signatures
        | CIinstance Id CQType
        -- CItype is imported abstractly
        | CItype IdK [Id] [Position] -- positions of use that caused export
        | CIclass (Maybe Bool) [CPred] IdK [Id] CFunDeps [Position] -- positions of use that caused export
        | CIValueSign Id CQType
        deriving (Eq, Ord, Show)

-- Since IdPKind is only expected in some disjuncts of CDefn, we could
-- create a separate IdPK for those cases, but that seems like overkill.
-- IdPKind in other locations will just be treated like IdK (no kind info).
data IdK
        = IdK Id
        | IdKind Id Kind
        -- this should not exist after typecheck
        | IdPKind Id PartialKind
        deriving (Eq, Ord, Show)

type CFunDeps = [([Id],[Id])]

-- Expressions
data CExpr
        = CLam (Either Position Id) CExpr
        | CLamT (Either Position Id) CQType CExpr
        | Cletseq [CDefl] CExpr -- rhs of "let x = x" refers to previous def
                                --   before current let or in earlier arm
        | Cletrec [CDefl] CExpr -- rhs of "let x = x" refers to self
        | CSelect CExpr Id                        -- expr, field id
        | CCon Id [CExpr]                        -- constructor id, arguments
        | Ccase Position CExpr CCaseArms
        -- Either a struct type or a constructor with named fields.
        -- The 'Maybe Bool' argument can indicate if it is specifically
        -- one or the other (True for struct), otherwise the typechecker
        -- will attempt to determine which is intended.
        | CStruct (Maybe Bool) Id [(Id, CExpr)]
        | CStructUpd CExpr [(Id, CExpr)]

        -- for hardware writes
        -- lhs <= rhs
        | Cwrite Position CExpr CExpr

        | CAny Position UndefKind
        | CVar Id
        | CApply CExpr [CExpr]
        | CTaskApply CExpr [CExpr] -- system task calls
        | CTaskApplyT CExpr CType [CExpr] -- type-checked $task (only $display) calls (the type is the inferred function type for the varargs task)
        | CLit CLiteral
        | CBinOp CExpr Id CExpr
        | CHasType CExpr CQType
        | Cif Position CExpr CExpr CExpr
        -- x[a]
        | CSub Position CExpr CExpr
        -- x[a:b]
        | CSub2 CExpr CExpr CExpr
        -- x[a:b] = y
        | CSubUpdate Position CExpr (CExpr, CExpr) CExpr
        | Cmodule Position [CMStmt]
        | Cinterface Position (Maybe Id) [CDefl]
        | CmoduleVerilog
              CExpr               -- expr for the module name (type String)
              Bool                -- whether it is a user-imported module
              VClockInfo          -- clocks
              VResetInfo          -- resets
              [(VArgInfo,CExpr)]  -- input arguments
              [VFieldInfo]        -- output interface fields
              VSchedInfo          -- scheduling annotations
              VPathInfo           -- path annotations
        | CForeignFuncC Id CQType -- link name, wrapped type
        | Cdo Bool CStmts        -- Bool indicates recursive binding
        | Caction Position CStmts
        | Crules [CSchedulePragma] [CRule]
        -- used before operator parsing
        | COper [COp]
        -- from deriving
        | CCon1 Id Id CExpr                        -- type id, con id, expr
        | CSelectTT Id CExpr Id                        -- type id, expr, field id
        -- INTERNAL in type checker
        | CCon0 (Maybe Id) Id                        -- type id, constructor id
        -- Not part of the surface syntax, used after type checking
        | CConT Id Id [CExpr]                        -- type id, constructor id, arguments
        | CStructT CType [(Id, CExpr)]
        | CSelectT Id Id                        -- type id, field id
        | CLitT CType CLiteral
        | CAnyT Position UndefKind CType
        | CmoduleVerilogT CType
              CExpr               -- expr for the module name (type String)
              Bool                -- whether it is a user-imported module
              VClockInfo          -- clocks
              VResetInfo          -- resets
              [(VArgInfo,CExpr)]  -- input arguments
              [VFieldInfo]        -- output interface fields
              VSchedInfo          -- scheduling annotations
              VPathInfo           -- path annotations
        | CForeignFuncCT Id CType -- link name, primitive type
        | CTApply CExpr [CType]
        -- for passing pprops as values
        | Cattributes [(Position,PProp)]
        deriving (Ord, Show)

instance Hyper CExpr where
    hyper x y = (x==x) `seq` y                -- XXX

-- ignore positions when testing equality
instance Eq CExpr where
    (==) (CLam (Left _) e1) (CLam (Left _) e2)
        = (e1 == e2)
    (==) (CLam (Right i1) e1) (CLam (Right i2) e2)
        = (i1 == i2) && (e1 == e2)
    (==) (CLamT (Left _) t1 e1) (CLamT (Left _) t2 e2)
        = (t1 == t2) && (e1 == e2)
    (==) (CLamT (Right i1) t1 e1) (CLamT (Right i2) t2 e2)
        = (i1 == i2) && (t1 == t2) && (e1 == e2)
    (==) (Cletseq ds1 e1) (Cletseq ds2 e2)
        = (ds1 == ds2) && (e1 == e2)
    (==) (Cletrec ds1 e1) (Cletrec ds2 e2)
        = (ds1 == ds2) && (e1 == e2)
    (==) (CSelect e1 i1) (CSelect e2 i2)
        = (e1 == e2) && (i1 == i2)
    (==) (CCon i1 es1) (CCon i2 es2)
        = (i1 == i2) && (es1 == es2)
    (==) (Ccase _ e1 as1) (Ccase _ e2 as2)
        = (e1 == e2) && (as1 == as2)
    (==) (CStruct mb1 i1 fs1) (CStruct mb2 i2 fs2)
        = (mb1 == mb2) && (i1 == i2) && (fs1 == fs2)
    (==) (CStructUpd e1 fs1) (CStructUpd e2 fs2)
        = (e1 == e2) && (fs1 == fs2)
    (==) (Cwrite _ x1 y1) (Cwrite _ x2 y2)
        = (x1 == x2) && (y1 == y2)
    (==) (CAny _ uk1) (CAny _ uk2)
        = (uk1 == uk2)  -- XXX ?
    (==) (CVar i1) (CVar i2)
        = (i1 == i2)
    (==) (CApply f1 es1) (CApply f2 es2)
        = (f1 == f2) && (es1 == es2)
    (==) (CTaskApply f1 es1) (CTaskApply f2 es2)
        = (f1 == f2) && (es1 == es2)
    (==) (CTaskApplyT f1 t1 es1) (CTaskApplyT f2 t2 es2)
        = (f1 == f2) && (t1 == t2) && (es1 == es2)
    (==) (CLit l1) (CLit l2)
        = (l1 == l2)
    (==) (CBinOp x1 i1 y1) (CBinOp x2 i2 y2)
        = (x1 == x2) && (i1 == i2) && (y1 == y2)
    (==) (CHasType e1 t1) (CHasType e2 t2)
        = (e1 == e2) && (t1 == t2)
    (==) (Cif _ c1 t1 e1) (Cif _ c2 t2 e2)
        = (c1 == c2) && (t1 == t2) && (e1 == e2)
    (==) (CSub _ x1 y1) (CSub _ x2 y2)
        = (x1 == x2) && (y1 == y2)
    (==) (CSub2 x1 y1 z1) (CSub2 x2 y2 z2)
        = (x1 == x2) && (y1 == y2) && (z1 == z2)
    (==) (CSubUpdate _ x1 y1 z1) (CSubUpdate _ x2 y2 z2)
        = (x1 == x2) && (y1 == y2) && (z1 == z2)
    (==) (Cmodule _ cs1) (Cmodule _ cs2)
        = (cs1 == cs2)
    (==) (Cinterface _ i1 ds1) (Cinterface _ i2 ds2)
        = (i1 == i2) && (ds1 == ds2)
    (==) (CmoduleVerilog i1 b1 c1 r1 as1 fs1 s1 p1)
         (CmoduleVerilog i2 b2 c2 r2 as2 fs2 s2 p2)
        = (i1 == i2) && (b1 == b2) && (c1 == c2) && (r1 == r2) &&
          (as1 == as2) && (fs1 == fs2) && (s1 == s2) && (p1 == p2)
    (==) (CForeignFuncC i1 t1) (CForeignFuncC i2 t2)
        = (i1 == i2) && (t1 == t2)
    (==) (Cdo b1 cs1) (Cdo b2 cs2)
        = (b1 == b2) && (cs1 == cs2)
    (==) (Caction _ cs1) (Caction _ cs2)
        = (cs1 == cs2)
    (==) (Crules ps1 rs1) (Crules ps2 rs2)
        = (ps1 == ps2) && (rs1 == rs2)
    (==) (COper os1) (COper os2)
       = (os1 == os2)
    (==) (CCon1 t1 c1 e1) (CCon1 t2 c2 e2)
       = (t1 == t2) && (c1 == c2) && (e1 == e2)
    (==) (CSelectTT t1 e1 f1) (CSelectTT t2 e2 f2)
        = (t1 == t2) && (e1 == e2) && (f1 == f2)
    (==) (CCon0 t1 c1) (CCon0 t2 c2)
        = (t1 == t2) && (c1 == c2)
    (==) (CConT t1 i1 es1) (CConT t2 i2 es2)
        = (t1 == t2) && (i1 == i2) && (es1 == es2)
    (==) (CStructT t1 fs1) (CStructT t2 fs2)
        = (t1 == t2) && (fs1 == fs2)
    (==) (CSelectT c1 f1) (CSelectT c2 f2)
        = (c1 == c2) && (f1 == f2)
    (==) (CLitT t1 l1) (CLitT t2 l2)
        = (t1 == t2) && (l1 == l2)
    (==) (CAnyT _ uk1 t1) (CAnyT _ uk2 t2)
        = (uk1 == uk2) && (t1 == t2)  -- XXX ?
    (==) (CmoduleVerilogT t1 i1 b1 c1 r1 as1 fs1 s1 p1)
         (CmoduleVerilogT t2 i2 b2 c2 r2 as2 fs2 s2 p2)
        = (t1 == t2) && (i1 == i2) && (b1 == b2) && (c1 == c2) && (r1 == r2) &&
          (as1 == as2) && (fs1 == fs2) && (s1 == s2) && (p1 == p2)
    (==) (CForeignFuncCT i1 t1) (CForeignFuncCT i2 t2)
        = (i1 == i2) && (t1 == t2)
    (==) (CTApply f1 ts1) (CTApply f2 ts2)
        = (f1 == f2) && (ts1 == ts2)
    (==) (Cattributes as1) (Cattributes as2)
        = (as1 == as2)
    (==) _ _
        = False

-- ===============

-- function called by the Classic parser to create a CmoduleVerilog
-- from a Classic "module verilog" (imported Verilog module)
xClassicModuleVerilog :: CExpr -> [(String, CExpr)] ->
                         [String] -> [String] ->
                         [(String, ([VeriPortProp], CExpr))] ->
                         [VFieldInfo] -> VSchedInfo -> VPathInfo ->
                         CExpr
xClassicModuleVerilog m params clocks resets ports methodinfo schedinfo pathinfo =
    -- get the current clock and reset and connect them to the imported module
    Cmodule (getPosition m)
            (clock_stmt ++
             reset_stmt ++
             [CMStmt (CSExpr Nothing
                     (xCmoduleVerilog m True -- it's a user import
                          (WireInfo clock_info reset_info arg_info)
                          args methodinfo' schedinfo pathinfo))])
  where param_ais   = map (Param . VName . fst) params
        param_args  = map snd params
        port_clock  = case clock_names of
                        []         -> Nothing
                        (clk_id:_) -> Just clk_id
        port_reset  = case reset_names of
                        []         -> Nothing
                        (rst_id:_) -> Just rst_id
        port_ais    =
            map (\p -> Port p port_clock port_reset)
                (zip (map (VName . fst) ports) (map (fst . snd) ports))
        port_args   = map (snd . snd) ports

        clock_stmt  =
            if (null clocks)
            then []
            else [CMStmt (bindVarT idClk tClock (CVar idExposeCurrentClock))]
        clock_exp   = CVar idClk
        -- only one Bluespec clock in Classic
        clock_args  = map (const clock_exp) clocks
        clock_names = map (addIdSuffix idClk) [1..(genericLength clocks)]
        clock_ais   = map ClockArg clock_names
        default_clk = listToMaybe clock_names -- Nothing if no clocks
        -- a single actual clock - no gating ancestors or siblings
        -- (The clock gate property is False, just to make life easier,
        -- because all module-verilog in the libs don't care about the gate)
        clock_info  =
            let mkInputClockInf i s = (i, Just (VName s, Left False))
            in  ClockInfo (zipWith mkInputClockInf clock_names clocks) [] [] []

        reset_stmt  =
            if (null resets)
            then []
            else [CMStmt (bindVarT idRst tReset (CVar idExposeCurrentReset))]
        reset_exp   = CVar idRst
        -- only one Bluespec reset in Classic
        reset_args  = map (const reset_exp) resets
        reset_names = map (addIdSuffix idRst) [1..(genericLength resets)]
        reset_ais   = map ResetArg reset_names
        -- Classic modules should have resets synchronized with their clock (if any)
        reset_info  =
            let mkInputResetInf i s = (i, (Just (VName s), default_clk))
            in  ResetInfo (zipWith mkInputResetInf reset_names resets) []
        default_rst = listToMaybe reset_names -- Nothing if no resets

        arg_info    = clock_ais  ++ reset_ais  ++ param_ais  ++ port_ais
        args        = clock_args ++ reset_args ++ param_args ++ port_args
        fixFieldClock m@(Method { vf_clock = Nothing }) = m { vf_clock = default_clk }
        fixFieldClock f = internalError ("xClassicModuleVerilog.fixFieldClock " ++ ppReadable f)
        fixFieldReset m@(Method { vf_reset = Nothing }) = m { vf_reset = default_rst }
        fixFieldReset f = internalError ("xClassicModuleVerilog.fixFieldReset " ++ ppReadable f)
        methodinfo' = map (fixFieldReset . fixFieldClock) methodinfo

-- ---------------

-- For a user module which is synthesized to Verilog,
-- this builds the "module verilog" wrapper for importing the Verilog module
-- back into Bluespec.
-- If the module takes a clock or reset, the current clock/reset is connected.
-- The wrapped CmoduleVerilog is marked as not being a user import
-- (since it's a synthesized module from Bluespec source).
xWrapperModuleVerilog :: Bool -> [PProp] -> CExpr -> VWireInfo -> [CExpr] ->
                         [VFieldInfo] -> VSchedInfo -> VPathInfo ->
                         CExpr
xWrapperModuleVerilog True pps m wireinfo args fields schedinfo pathinfo =
    -- it's a foreign function, which needs to clock or reset
    xCmoduleVerilog m False wireinfo args fields schedinfo pathinfo
xWrapperModuleVerilog False pps m wireinfo args fields schedinfo pathinfo =
  let (args1,stmts1) =
          if (hasDefaultClk pps)
          then ([CVar idClk],
                [CMStmt (bindVarT idClk tClock (CVar idExposeCurrentClock))])
          else ([],[])
      (args2,stmts2) =
          if (hasDefaultRst pps)
          then ([CVar idRst],
                [CMStmt (bindVarT idRst tReset (CVar idExposeCurrentReset))])
          else ([],[])
      args'  = args ++ args1 ++ args2
      stmts' = stmts1 ++ stmts2 ++
               [CMStmt (CSExpr Nothing
                        (xCmoduleVerilog m False -- it's not a user import
                             wireinfo args' fields schedinfo pathinfo))]
  in Cmodule (getPosition m) stmts'

-- ---------------

-- The core of the above functions
xCmoduleVerilog :: CExpr -> Bool -> VWireInfo -> [CExpr] ->
                   [VFieldInfo] -> VSchedInfo -> VPathInfo ->
                   CExpr
xCmoduleVerilog m is_user_import wireinfo args fields schedinfo pathinfo =
 let arginfo = wArgs wireinfo in
    if (length args) == (length arginfo) then
      CmoduleVerilog m
                     is_user_import
                     (wClk wireinfo)
                     (wRst wireinfo)
                     (zip arginfo args)
                     fields -- methods or clocks
                     schedinfo
                     pathinfo -- VPathInfo
    else
      internalError
          ("CSyntax.xCmoduleVerilog: args and arginfo do not match: " ++
           (ppReadable args) ++ (ppReadable arginfo))


-- ===============

data CLiteral = CLiteral Position Literal deriving (Show)
instance Eq CLiteral where
        CLiteral _ l == CLiteral _ l'  =  l == l'
instance Ord CLiteral where
        CLiteral _ l `compare` CLiteral _ l'  =  l `compare` l'

data COp
        = CRand CExpr    -- operand
        | CRator Int Id  -- infix operator Id, Int is the number of arguments?
        deriving (Eq, Ord, Show)

type CSummands = [CInternalSummand]

-- summand in internal form (each summand only takes a single argument
-- whose type is CType)
-- Data constructors can have multiple names for a constructor (for backwards
-- compatibility with old names), but the first name is the primary name
-- (used in compiler output etc).
data CInternalSummand =
    CInternalSummand { cis_names :: [Id],
                       cis_arg_type :: CType,
                       cis_tag_encoding :: Integer }
    deriving (Eq, Ord, Show)

-- return only the primary name
getCISName :: CInternalSummand -> Id
getCISName cis = case (cis_names cis) of
                     [] -> internalError "getCISName: empty cis_names"
                     (cn:_) -> cn

-- original summands (taking a list of arguments, each of whose types
-- is given by CQType); the Int is a hack to support Enums with
-- noncontiguous Bits encodings
-- Data constructors can have multiple names for a constructor (for backwards
-- compatibility with old names), but the first name is the primary name
-- (used in compiler output etc).
type COSummands = [COriginalSummand]

data COriginalSummand =
    COriginalSummand { cos_names :: [Id],
                       cos_arg_types :: [CQType],
                       cos_field_names :: Maybe [Id],
                       cos_tag_encoding :: Maybe Integer }
    deriving (Eq, Ord, Show)

-- return only the primary name
getCOSName :: COriginalSummand -> Id
getCOSName cos = case (cos_names cos) of
                     [] -> internalError "getCOSName: empty cos_names"
                     (cn:_) -> cn

-- if CQType is a function, [IfcPragmas] (if present) lists argument names
-- (used by the backend to generate pretty names for module ports)
data CField = CField { cf_name :: Id,
                       cf_pragmas :: Maybe [IfcPragma],
                       cf_type :: CQType,
                       cf_default :: [CClause],
                       cf_orig_type :: Maybe CType
                     }
              deriving (Eq, Ord, Show)

type CFields = [CField] -- just a list of CField

-- redundant
--type Ids = [Id]
data CCaseArm = CCaseArm { cca_pattern :: CPat,
                           cca_filters :: [CQual],
                           cca_consequent :: CExpr }
              deriving (Eq, Ord, Show)

type CCaseArms = [CCaseArm] -- [(CPat, [CQual], CExpr)]

data CStmt
          -- bind cexpr of type cqtype to cpat; id, if present, is instance name
        = CSBindT CPat (Maybe CExpr) [(Position,PProp)] CQType CExpr
          -- bind cexpr to cpat; id, if present, is instance name
        | CSBind CPat (Maybe CExpr) [(Position,PProp)] CExpr
        | CSletseq [CDefl] -- rhs of "let x = x" refers to previous def
                           --   before current let or in earlier arm
        | CSletrec [CDefl] -- rhs of "let x = x" refers to self
        | CSExpr (Maybe CExpr) CExpr
        deriving (Eq, Ord, Show)

bindVarT :: Id -> CType -> CExpr -> CStmt
bindVarT i t e = CSBindT (CPVar i) Nothing [] (CQType [] t) e

type CStmts = [CStmt]

data CMStmt
        = CMStmt CStmt
        | CMrules CExpr
        | CMinterface CExpr
        | CMTupleInterface Position [CExpr]
        deriving (Eq, Ord, Show)

data CRule
        = CRule [RulePragma] (Maybe CExpr) [CQual] CExpr
        | CRuleNest [RulePragma] (Maybe CExpr) [CQual] [CRule]
        deriving (Eq, Ord, Show)

-- | A definition with a binding. Can occur as a let expression, let statement
-- in a do block, a typeclass instance defn, or bindings in an interface.
data CDefl                -- [CQual] part is the when clause used in an interface
                          -- binding, ie the explicit condition attached to each method
        = CLValueSign CDef [CQual]     -- let x :: T = e2 -- explicit type sig
        | CLValue Id [CClause] [CQual] -- let y = e2      -- no explicit type sig
        | CLMatch CPat CExpr           -- let [z] = e3
        deriving (Eq, Ord, Show)

-- Definition, local or global
data CDef
        = CDef Id CQType [CClause]                        -- before type checking
        | CDefT Id [TyVar] CQType [CClause]                -- after type checking, with type variables from the CQType
        deriving (Eq, Ord, Show)

-- Definition clause
-- each interface's definitions (within the module) correspond to one of these
data CClause
        = CClause [CPat]                -- arguments (including patterns)
                  [CQual]               -- qualifier on the args
                  CExpr                 -- the body
        deriving (Eq, Ord, Show)

-- Pattern matching
data CQual
        = CQGen CType CPat CExpr
        | CQFilter CExpr
        deriving (Eq, Ord, Show)

isCQFilter :: CQual -> Bool
isCQFilter (CQFilter _) = True
isCQFilter _            = False

data CPat
        = CPCon Id [CPat]
        -- Either a struct type or a constructor with named fields.
        -- The 'Maybe Bool' argument can indicate if it is specifically
        -- one or the other (True for struct), otherwise the typechecker
        -- will attempt to determine which is intended.
        | CPstruct (Maybe Bool) Id [(Id, CPat)]
        | CPVar Id
        | CPAs Id CPat
        | CPAny Position
        | CPLit CLiteral
        -- position, base, [(length, value or don't-care)] starting from MSB
        -- note that length is length in digits, not bits!
        | CPMixedLit Position Integer [(Integer, Maybe Integer)]
        -- used before operator parsing
        | CPOper [CPOp]
        -- generated by deriving code
        | CPCon1 Id Id CPat                        -- first Id is type of constructor
        -- After type checking
        | CPConTs Id Id [CType] [CPat]
        deriving (Eq, Ord, Show)

data CPOp
        = CPRand CPat
        | CPRator Int Id
        deriving (Eq, Ord, Show)

newtype CInclude
       = CInclude String
    deriving (Eq, Ord, Show)
--------
-- Utilities

impName :: CImport -> Id
impName (CImpId _ i) = i
impName (CImpSign _ _ (CSignature i _ _ _)) = i

-- swapped order of (CVar i) es and e [] patterns
-- to make optional default arguments for $finish and $stop work
cmtApply :: Int -> CExpr -> [CExpr] -> CExpr
cmtApply n e@(CVar i) es | isTaskName (getIdBaseString i) = CTaskApply e es
cmtApply n e es = cApply (100 + n) e es

cApply :: Int -> CExpr -> [CExpr] -> CExpr
cApply n e [] = e
cApply n (CCon i es) es' = CCon i (es ++ es')
cApply n (CConT t i es) es' = CConT t i (es ++ es')
cApply n (CApply e es) es' = CApply e (es ++ es')
cApply n (CTaskApply e es) es' = CTaskApply e (es ++ es')
cApply n e as = CApply e as

cVApply :: Id -> [CExpr] -> CExpr
cVApply i es | isTaskName (getIdBaseString i) =
    internalError $ "cVApply to " ++ (show i) ++ "\n"
cVApply i es = cApply 2 (CVar i) es

cVar :: Id -> CExpr
cVar name | isTaskName (getIdBaseString name) = CTaskApply (CVar name) []
          | otherwise = CVar name

-- tasks start with $ followed by a letter
isTaskName :: String -> Bool
isTaskName ('$':c:_) = isAlpha c
isTaskName _ = False

cTApply :: CExpr -> [CType] -> CExpr
cTApply f [] = f
cTApply f ts = CTApply f ts

getName :: CDefn -> Either Position Id
getName (CValue i _) = Right i
getName (CValueSign (CDef i _ _)) = Right i
getName (CValueSign (CDefT i _ _ _)) = Right i
getName (Cprimitive i _) = Right i
getName (CprimType i) = Right $ iKName i
getName (CPragma pr) = Left $ getPosition pr
getName (Cforeign { cforg_name = i }) = Right i
getName (Ctype i _ _) = Right $ iKName i
getName (Cdata { cd_name = name }) = Right $ iKName name
getName (Cstruct _ _ i _ _ _) = Right $ iKName i
getName (Cclass _ _ i _ _ _) = Right $ iKName i
getName (Cinstance qt _) = Left $ getPosition qt
getName (CItype i _ _) = Right $ iKName i
getName (CIclass _ _ i _ _ _) = Right $ iKName i
getName (CIinstance _ qt) = Left $ getPosition qt
getName (CIValueSign i _) = Right i

getDName :: CDef -> Id
getDName (CDef i _ _) = i
getDName (CDefT i _ _ _) = i

getLName :: CDefl -> Id
getLName (CLValueSign def _) = getDName def
getLName (CLValue i _ _) = i
getLName (CLMatch _ _) = internalError "CSyntax.getLName: CLMatch"

iKName :: IdK -> Id
iKName (IdK i) = i
iKName (IdKind i _) = i
iKName (IdPKind i _) = i

isTDef :: CDefn -> Bool
isTDef (Ctype _ _ _) = True
isTDef (Cdata {}) = True
isTDef (Cstruct _ _ _ _ _ _) = True
isTDef (Cclass _ _ _ _ _ _) = True
isTDef (CItype _ _ _) = True
isTDef (CIclass _ _ _ _ _ _) = True
isTDef (CprimType _) = True
isTDef _ = False

getNK :: Integer -> Kind -> [Kind]
getNK 0 k = []
getNK n (Kfun a r) = a : getNK (n-1) r
getNK n k = internalError ("getNK: " ++ ppReadable (n, k))

anyExprAt :: Position -> CExpr
anyExprAt pos = CAny pos UDontCare

anyExpr :: CExpr
anyExpr = anyExprAt noPosition

anyTExpr :: CType -> CExpr
anyTExpr t = CAnyT noPosition UDontCare t

--------

pp :: (PPrint a) => PDetail -> a -> Doc
pp d x = pPrint d 0 x

t :: String -> Doc
t s = text s

------
-- Position information

instance HasPosition IdK where
    getPosition (IdK i) = getPosition i
    getPosition (IdKind i _) = getPosition i
    getPosition (IdPKind i _) = getPosition i

instance HasPosition CPat where
    getPosition (CPCon c _) = getPosition c
    getPosition (CPstruct _ c _) = getPosition c
    getPosition (CPVar i) = getPosition i
    getPosition (CPAs i _) = getPosition i
    getPosition (CPAny p) = p
    getPosition (CPLit l) = getPosition l
    getPosition (CPMixedLit p _ _) = p
    getPosition (CPOper ps) = getPosition ps
    getPosition (CPCon1 _ c _) = getPosition c
    getPosition (CPConTs _ c _ _) = getPosition c

instance HasPosition CPOp where
    getPosition (CPRand p) = getPosition p
    getPosition (CPRator _ i) = getPosition i

instance HasPosition CClause where
    getPosition (CClause ps qs e) = getPosition (ps, qs, e)

instance HasPosition CQual where
    getPosition (CQGen _ p _) = getPosition p
    getPosition (CQFilter e) = getPosition e

instance HasPosition CExpr where
    getPosition (CLam ei _) = getPosition ei
    getPosition (CLamT ei _ _) = getPosition ei
    getPosition (Cletseq ds e) = getPosition (ds, e)
    getPosition (Cletrec ds e) = getPosition (ds, e)
    getPosition (CSelect e _) = getPosition e
    getPosition (CSelectTT _ e _) = getPosition e
    getPosition (CCon c _) = getPosition c
    getPosition (Ccase pos _ _) = pos
    getPosition (CStruct _ i _) = getPosition i
    getPosition (CStructUpd e _) = getPosition e
    getPosition (Cwrite pos _ _) = pos
    getPosition (CAny pos _) = pos
    getPosition (CVar i) = getPosition i
    getPosition (CApply e _) = getPosition e
    getPosition (CTaskApply e _) = getPosition e
    getPosition (CTaskApplyT e _ _) = getPosition e
    getPosition (CLit l) = getPosition l
    getPosition (CBinOp e _ _) = getPosition e
    getPosition (CHasType e _) = getPosition e
    getPosition (Cif pos _ _ _) = pos
    getPosition (CSub pos _ _) = pos
    getPosition (CSub2 e _ _) = getPosition e
    getPosition (CSubUpdate pos _ _ _) = pos
    getPosition (CCon1 _ c _) = getPosition c
    getPosition (Cmodule pos _) = pos
    getPosition (Cinterface pos i ds) = pos
    getPosition (CmoduleVerilog e _ _ _ ses fs _ _) =
        getPosition (e, map snd ses, fs)
    getPosition (CmoduleVerilogT _ e _ _ _ ses fs _ _) =
        getPosition (e, map snd ses, fs)
    getPosition (CForeignFuncC i _) = getPosition i
    getPosition (CForeignFuncCT i _) = getPosition i
    getPosition (Cdo _ ss) = getPosition ss
    getPosition (Caction pos ss) = pos
    getPosition (Crules _ rs) = getPosition rs
    getPosition (COper es) = getPosition es
    getPosition (Cattributes pps) =
        -- take the position of the first pprop with a good position
        getPosition (map fst pps)
    --
    getPosition (CTApply e ts) = getPosition (e, ts)
    getPosition (CConT _ c _) = getPosition c
    getPosition (CCon0 _ c) = getPosition c
    getPosition (CSelectT _ i) = getPosition i
    getPosition (CLitT _ l) = getPosition l
    getPosition (CAnyT pos _ _) = pos
    getPosition e = internalError ("no match in getPosition: " ++ ppReadable e)

instance HasPosition COp where
    getPosition (CRand e) = getPosition e
    getPosition (CRator _ i) = getPosition i

instance HasPosition CLiteral where
    getPosition (CLiteral p _) = p

instance HasPosition CStmt where
    getPosition (CSBindT p i pps t e) = getPosition p
    getPosition (CSBind p i pps e) = getPosition p
    getPosition (CSletseq ds) = getPosition ds
    getPosition (CSletrec ds) = getPosition ds
    getPosition (CSExpr _ e) = getPosition e

instance HasPosition CMStmt where
    getPosition (CMStmt s) = getPosition s
    getPosition (CMrules e) = getPosition e
    getPosition (CMinterface e) = getPosition e
    getPosition (CMTupleInterface pos e) = pos

instance HasPosition CDefl where
    getPosition (CLValueSign d _) = getPosition d
    getPosition (CLValue i _ _) = getPosition i
    getPosition (CLMatch p e) = getPosition (p, e)

instance HasPosition CDef where
    getPosition (CDef i _ _) = getPosition i
    getPosition (CDefT i _ _ _) = getPosition i

instance HasPosition CDefn where
    getPosition d = getPosition (getName d)

instance HasPosition CRule where
    getPosition (CRule _ i qs e) = getPosition (i, qs, e)
    getPosition (CRuleNest _ i qs rs) = getPosition (i, qs, rs)

instance HasPosition CCaseArm where
    getPosition arm =
        getPosition (cca_pattern arm) `bestPosition`
        getPosition (cca_filters arm) `bestPosition`
        getPosition (cca_consequent arm)

instance HasPosition CInternalSummand where
    getPosition summand = getPosition (cis_names summand)

------

--------

-- Pretty printing

ppExports :: PDetail -> Either [CExport] [CExport] -> Doc
ppExports d (Right []) = empty
ppExports d (Right noexps) = t " hiding (" <> sepList (map (pp d) noexps) (t",") <> t")"
ppExports d (Left exports) = t "(" <> sepList (map (pp d) exports) (t",") <> t")"

instance PPrint CPackage where
    pPrint d _ (CPackage i exps imps fixs def includes) =
        (t"package" <+> ppConId d i <> ppExports d exps <+> t "where {") $+$
        pBlock d 0 True (map (pp d) imps ++ map (pp d) fixs ++ map (pp d) def ++ map (pp d) includes)

instance PPrint CExport where
    pPrint d p (CExpVar i) = ppVarId d i
    pPrint d p (CExpCon i) = ppConId d i
    pPrint d p (CExpConAll i) = ppConId d i <> t"(..)"
    pPrint d p (CExpPkg i) = t"package" <+> ppId d i

instance PPrint CImport where
    pPrint d p (CImpId q i) = t"import" <+> ppQualified q <+> ppConId d i
    pPrint d p (CImpSign _ q (CSignature i _ _ _)) = t"import" <+> ppQualified q <+> ppConId d i <+> t "..."

ppQualified :: Bool -> Doc
ppQualified True = text "qualified"
ppQualified False = empty

instance PPrint CSignature where
    pPrint d _ (CSignature i imps fixs def) =
        (t"signature" <+> ppConId d i <+> t "where" <+> t "{") $+$
        pBlock d 0 True (map pi imps ++ map (pp d) fixs ++ map (pp d) def)
      where pi i = t"import" <+> ppConId d i

instance PPrint CFixity where
    pPrint d _ (CInfix  p i) = text "infix"  <+> text (show p) <+> ppInfix d i
    pPrint d _ (CInfixl p i) = text "infixl" <+> text (show p) <+> ppInfix d i
    pPrint d _ (CInfixr p i) = text "infixr" <+> text (show p) <+> ppInfix d i

instance PPrint CDefn where
    pPrint d p (Ctype i as ty) =
        sep [sep ((t"type" <+> ppConIdK d i) : map (nest 2 . ppVarId d) as) <+> t "=",
                  nest 2 (pp d ty)]
    pPrint d p (Cdata { cd_visible = vis,
                        cd_name = i,
                        cd_type_vars = as,
                        cd_original_summands = cs@(_:_),
                        cd_internal_summands = [],
                        cd_derivings = ds }) =                -- a hack to print original constructors
        sep [sep ((t"data" <+> ppConIdK d i) : map (nest 2 . ppVarId d) as) <> t(if vis then " =" else " =="),
                  nest 2 (ppOSummands d cs)]
    pPrint d p (Cdata { cd_visible = vis,
                        cd_name = i,
                        cd_type_vars = as,
                        cd_internal_summands = cs,
                        cd_derivings = ds }) =
        sep [sep ((t"data" <+> ppConIdK d i) : map (nest 2 . ppVarId d) as) <> t(if vis then " =" else " =="),
                  nest 2 (ppSummands d cs)]
        <> ppDer d ds
    pPrint d p (Cstruct vis (SInterface prags) i as fs ds) =
        (t("interface ") <> sep (ppConIdK d i : map (nest 2 . ppVarId d) as) <+> ppIfcPragma d prags <+> t(if vis then "= {" else "== {")) $+$
        pBlock d 4 False (map (ppField d) fs) <> ppDer d ds
    pPrint d p (Cstruct vis ss i as fs ds) =
        (t("struct ") <> sep (ppConIdK d i : map (nest 2 . ppVarId d) as) <+> t(if vis then "= {" else "== {")) $+$
        pBlock d 4 False (map (ppField d) fs) <> ppDer d ds
    pPrint d p (Cclass incoh ps ik is fd ss) =
        (t_cls <+> ppPreds d ps (sep (ppConIdK d ik : map (ppVarId d) is)) <> ppFDs d fd <+> t "where {") $+$
        pBlock d 4 False (map (ppField d) ss)
      where t_cls = case incoh of
                     Just False -> t"class coherent"
                     Just True  -> t"class incoherent"
                     Nothing    -> t"class"
    pPrint d p (Cinstance qt ds) =
        (t"instance" <+> pPrint d 0 qt <+> t "where {") $+$
        pBlock d 4 False (map (pPrint d 0) ds)
    pPrint d p (CValueSign def) = pPrint d p def
    pPrint d p (CValue i cs) =
        vcat (map (\ cl -> ppClause d p [ppVarId d i] cl <> t";") cs)
    pPrint d p (Cprimitive i ty) =
        text "primitive" <+> ppVarId d i <+> t "::" <+> pp d ty
    pPrint d p (CPragma pr) = pPrint d p pr
    pPrint d p (CprimType ik) =
        t"primitive type" <+>
        -- don't use ppConIdK because this syntax has no parentheses
        case (ik) of
            (IdK i)        -> ppConId d i
            (IdKind i k)   -> ppConId d i <+> t "::" <+> pp d k
            (IdPKind i pk) -> ppConId d i <+> t "::" <+> pp d pk
    pPrint d p (Cforeign i ty oname opnames _) =
        text "foreign" <+> ppVarId d i <+> t "::" <+> pp d ty <>
        (case oname of Nothing -> text ""; Just s -> text (" = " ++ show s)) <>
        (case opnames of Nothing -> text ""; Just (is, os) -> t"," <> pparen True (sep (map (text . show) is ++ po os)))
      where po [o] = [text ",", text (show o)]
            po os = [t"(" <> sepList (map (text . show) os) (t",") <> t ")"]
    pPrint d p (CIinstance i qt) =
        t"instance" <+> ppConId d i <+> pPrint d 0 qt
    pPrint d p (CItype i as positions) =
        sep (t"type" <+> ppConIdK d i : map (nest 2 . ppVarId d) as)
    pPrint d p (CIclass incoh ps ik is fd positions) =
        t_cls <+> ppPreds d ps (sep (ppConIdK d ik : map (nest 2 . ppVarId d) is)) <> ppFDs d fd
      where t_cls = case incoh of
                     Just False -> t"class coherent"
                     Just True  -> t"class incoherent"
                     Nothing    -> t"class"
    pPrint d p (CIValueSign i ty) = ppVarId d i <+> t "::" <+> pp d ty

instance PPrint CField where
    pPrint d p f = ppField d f

ppField :: PDetail -> CField -> Doc
ppField detail field =
  let fid = cf_name field
      dfl = cf_default field
  in
    (ppVarId detail fid <+> t "::" <+> pp detail (cf_type field)
        <+> maybe empty (ppIfcPragma detail) (cf_pragmas field) <>
        if (null dfl) then empty else text ";") $$
    -- display the default, if it exists
    if (null dfl)
     then empty
     else let ppC cl = ppClause detail 0 [ppVarId detail fid] cl
          in  foldr1 (\ x y -> x <> text ";" $$ y) (map ppC dfl)
    -- XXX not including orig_type

ppIfcPragma :: PDetail -> [IfcPragma] -> Doc
ppIfcPragma detail [] = empty
ppIfcPragma detail ps =
        text "{-#" <+>
        sep (punctuate comma (map (pPrint detail 0) ps ) )
        <+> text "#-}"

ppFDs :: PDetail -> CFunDeps -> Doc
ppFDs d [] = empty
ppFDs d fd = text " |" <+> sepList (map (ppFD d) fd) (t",")

ppFD :: PDetail -> ([Id], [Id]) -> Doc
ppFD d (as,rs) = sep (ppVarId d <$> as) <+> t "->" <+> sep (ppVarId d <$> rs)

ppPreds :: PDetail -> [CPred] -> Doc -> Doc
ppPreds d [] x = x
ppPreds d preds x = t "(" <> sepList (map (pPrint d 0) preds) (t ",") <> t ") =>" <+> x

ppConIdK :: PDetail -> IdK -> Doc
ppConIdK d (IdK i) = ppConId d i
ppConIdK d (IdKind i k) = pparen True $ ppConId d i <+> t "::" <+> pp d k
ppConIdK d (IdPKind i pk) = pparen True $ ppConId d i <+> t "::" <+> pp d pk

instance PPrint IdK where
    pPrint d p (IdK i) = pPrint d p i
    pPrint d p (IdKind i k) = pparen True $ pp d i <+> t "::" <+> pp d k
    pPrint d p (IdPKind i pk) = pparen True $ pp d i <+> t "::" <+> pp d pk

pBlock :: PDetail -> Int -> Bool -> [Doc] -> Doc
pBlock _ n _ [] = t"}"
pBlock _ n nl xs =
        (t (replicate n ' ') <>
        foldr1 ($+$) (map (\ x -> x <> if nl then t";" $+$ t"" else t";") (init xs) ++ [last xs])) $+$
        t"}"

ppDer :: PDetail -> [CTypeclass] -> Doc
ppDer d [] = text ""
ppDer d is = text " deriving (" <> sepList (map (pPrint d 0) is) (text ",") <> text ")"


instance PPrint CExpr where
    pPrint d p (CLam ei e) = ppQuant "\\ "  d p ei e
    pPrint d p (CLamT ei ty e) = ppQuant "\\ "  d p ei e
    pPrint d p (Cletseq [] e) = pparen (p > 0) $
        (t"letseq in" <+> pp d e)
    pPrint d p (Cletseq ds e) = pparen (p > 0) $
        (t"letseq" <+> text "{" <+> foldr1 ($+$) (map (pp d) ds)) <+> text "}" $+$
        (t"in  " <> pp d e)
    pPrint d p (Cletrec [] e) = pparen (p > 0) $
        (t"let in" <+> pp d e)
    pPrint d p (Cletrec ds e) = pparen (p > 0) $
        (t"let" <+> text "{" <+> foldr1 ($+$) (map (pp d) ds)) <+> text "}" $+$
        (t"in  " <> pp d e)
    pPrint d p (CSelect e i) = pparen (p > (maxPrec+2)) $ pPrint d (maxPrec+2) e <> t"." <> ppVarId d i
    pPrint d p (CCon i []) = ppConId d i
    pPrint d p (CCon i es) = pPrint d p (CApply (CCon i []) es)
    pPrint d p (Ccase pos e arms) = pparen (p > 0) $ ppCase d e arms
    pPrint d p (CAny {}) = text "_"
    pPrint d p (CVar i) = ppVarId d i
    pPrint d p (CStruct _ tyc []) | tyc == idPrimUnit = text "()"
    pPrint d p (CStruct _ tyc ies) = pparen (p > 0) $ pPrint d (maxPrec+1) tyc <+> t "{" <+> sepList (map f ies ++ [t"}"]) (t";")
        where f (i, e) = ppVarId d i <+> t "=" <+> pp d e
    pPrint d p (CStructUpd e ies) = pparen (p > 0) $ pPrint d (maxPrec+1) e <+> t "{" <+> sepList (map f ies ++ [t"}"]) (t";")
        where f (i, e) = ppVarId d i <+> t "=" <+> pp d e
    pPrint d p (Cwrite _ e v)  = pparen (p > 0) $ pPrint d (maxPrec+1) e <+> t ":=" <+> pPrint d p v
    pPrint PDReadable p (CApply e []) = pPrint PDReadable p e
    pPrint d p (CApply e es) = pparen (p>(maxPrec-1)) $
        sep (pPrint d (maxPrec-1) e : map (nest 2 . ppApArg) es)
        where ppApArg e = pPrint d maxPrec e
    pPrint d p (CTaskApply e es) = pparen (p>(maxPrec-1)) $
        sep (pPrint d (maxPrec-1) e : map (nest 2 . ppApArg) es)
        where ppApArg e = pPrint d maxPrec e
    -- XXX: should include t?
    pPrint d p (CTaskApplyT e t es) = pparen (p>(maxPrec-1)) $
        sep (pPrint d (maxPrec-1) e : map (nest 2 . ppApArg) es)
        where ppApArg e = pPrint d maxPrec e
    pPrint d p (CLit l) = pPrint d p l
    pPrint d p (CBinOp e1 i e2) = ppOp d p i e1 e2
    pPrint d p (CHasType e t) = pparen (p>0) $ pPrint d maxPrec e <> text "::" <> pPrint d maxPrec t
    pPrint d p (Cif pos c tr e) = pparen (p>0) (sep [t"if" <+> pp d c <+> t "then", nest 4 (pp d tr), t"else", nest 4 (pp d e)])
    pPrint d p (CSub pos e s) = pPrint d maxPrec e <> t"[" <> pp d s <> t"]"
    pPrint d p (CSub2 e h l) = pPrint d maxPrec e <> t"[" <> pp d h <> t":" <> pp d l <> t"]"
    pPrint d p (CSubUpdate pos e (h, l) rhs) = pPrint d p (CSub2 e h l) <> t"=" <> pPrint d maxPrec rhs
    pPrint d p (Cmodule _ is) = t"module {" $+$ pBlock d 2 False (map (pp d) is)
    pPrint d p (Cinterface pos Nothing ds) =
        pparen (p>0) (t"interface {" $+$ pBlock d 2 False (map (pp d) ds))
    pPrint d p (Cinterface pos (Just i) ds) =
        pparen (p>0) (t"interface" <+> pp d i <+> t "{" $+$ pBlock d 2 False (map (pp d) ds))
    pPrint d p (CmoduleVerilog m ui c r ses fs sch ps) =
        sep [
          t"module verilog" <+> pp d m <+>
          pp d c <> t"" <+> pp d r <+> t"",
          nest 4 (if null ses then t"" else pparen True (sepList (map ppA ses) (t","))),
          nest 4 (t"{" $+$ pBlock d 2 False (map f fs)),
          nest 4 (pp d sch) ]
          where mfi s Nothing = empty
                mfi s (Just i) = t s <+> ppVarId d i
                mfp s Nothing = empty
                mfp s (Just (VName s', _)) = t s <+> t s'
                f (Clock i) = t "clock_field " <> ppVarId d i
                f (Reset i) = t "reset_field " <> ppVarId d i
                f (Inout i (VName p) mc mr) =
                    t "inout_field " <> ppVarId d i <+> t p <+>
                    mfi "clocked_by" mc <+> mfi "reset_by" mr
                f (Method i mc mr n ps mo me) =
                    ppVarId d i <> g n <+> t "=" <+> t (unwords (map h ps)) <+>
                    mfi "clocked_by" mc <+> mfi "reset_by" mr <+> mfp "output" mo <+> mfp "enable" me
                g 1 = t""
                g n = t("[" ++ itos n ++ "]")
                h (s,[]) = show s
                h (s,ps) = show s ++ "{" ++ intercalate "," (map (drop 2 . show) ps) ++ "}"
                ppA (ai, e) = text "(" <> text (ppReadable ai) <> text "," <+> pp d e <> text ")"
    pPrint d p (CForeignFuncC i wrap_ty) =
        -- There's no real Classic syntax for this:
        t"ForeignFuncC" <+> pp d i
    pPrint d p (Cdo _ ss) = pparen (p>0) $ t "do" <+> t "{" <+> sepList (map (pPrint d 0) ss ++ [t"}"]) (t";")
    pPrint d p (Caction _ ss) = pparen (p>0) $ t "action" <+> t "{" <+> sepList (map (pPrint d 0) ss ++ [t"}"]) (t";")
    pPrint d p (Crules [] rs) = pparen (p>0) $ t"rules {" $+$ pBlock d 2 False (map (pp d) rs)
    pPrint d p (Crules ps rs) = pPrint d p ps $+$
                                (pparen (p>0) $ t"rules {" $+$ pBlock d 2 False (map (pp d) rs))
    pPrint d p (COper ops) = pparen (p > maxPrec-1) (sep (map (pPrint d (maxPrec-1)) ops))
    ----
    pPrint d p (CCon1 _ i e) = pPrint d p (CCon i [e])
    pPrint d p (CSelectTT _ e i) = pparen (p > (maxPrec+2)) $ pPrint d (maxPrec+2) e <> t"." <> ppVarId d i
    ----
    pPrint d p (CCon0 _ i) = ppConId d i
    ----
    pPrint d p (CConT _ i es) = pPrint d p (CCon i es)
    pPrint d p (CStructT ty ies) = pPrint d p (CStruct (Just True) tyc ies)
        where tyc = fromJustOrErr "pPrint CStructT" (leftCon ty)
    pPrint d p (CSelectT _ i) = text "." <> ppVarId d i
    pPrint d p (CLitT _ l) = pPrint d p l
    pPrint d p (CAnyT pos uk t) = text "_"
    pPrint d p (CmoduleVerilogT _ m ui c mr ses fs sch ps) = pPrint d p (CmoduleVerilog m ui c mr ses fs sch ps)
    pPrint d p (CForeignFuncCT i prim_ty) = t"ForeignFuncC" <+> pp d i
    pPrint d p (CTApply e ts) = pparen (p>(maxPrec-1)) $
        sep (pPrint d (maxPrec-1) e : map (nest 2 . ppApArg) ts)
        where ppApArg ty = t"\183" <> pPrint d maxPrec ty
    pPrint d p (Cattributes pps) = pparen True $ text "Attributes" <+> pPrint d 0 (map snd pps)

instance PPrint CLiteral where
    pPrint d p (CLiteral _ l) = pPrint d p l

instance PPrint CStmt where
    pPrint d p (CSBindT pat inst pprops ty e) =
        foldr ($+$) empty $
            (map (ppPProp d . snd) pprops) ++
            [pp d pat <+> t "::" <+> pp d ty <+> t "<-" <+> pp d e]
    pPrint d p (CSBind pat inst pprops e) =
        foldr ($+$) empty $
            (map (ppPProp d . snd) pprops) ++
            [pp d pat <+> t "<-" <+> pp d e]
    pPrint d p (CSletseq []) = internalError "CSyntax.PPrint(CStmt): CSletseq []"
    pPrint d p (CSletseq ds) = text "letseq" <+> text "{" <+> foldr1 ($+$) (map (pp d) ds) <+> text "}"
    pPrint d p (CSletrec []) = internalError "CSyntax.PPrint(CStmt): CSletrec []"
    pPrint d p (CSletrec ds) = text "let" <+> text "{" <+> foldr1 ($+$) (map (pp d) ds) <+> text "}"
    pPrint d p (CSExpr _ e) = pPrint d p e

instance PPrint CMStmt where
    pPrint d p (CMStmt s) = pPrint d p s
    pPrint d p (CMrules e) = pPrint d p e
    pPrint d p (CMinterface e) = pPrint d p (cVApply (idReturn (getPosition e)) [e])
    pPrint d p (CMTupleInterface _ es) = text"(" <> sepList (map (pPrint d p) es) (text ",") <> text ")"

instance PPrint COp where
    pPrint d _ (CRand p) = pp d p
    pPrint d _ (CRator _ i) = ppInfix d i

ppQuant :: String -> PDetail -> Int -> Either Position Id -> CExpr -> Doc
ppQuant s d p ei e =
    let ppI (Left _) = text "_"
        ppI (Right i) = pPrint d 0 i
    in  pparen (p>0) (sep [t s <> ppI ei <+> t "->", pp d e])

ppCase :: PDetail -> CExpr -> [CCaseArm] -> Doc
ppCase detail scrutinee arms =
    (t"case" <+> pp detail scrutinee <+> t "of {") $+$
    pBlock detail 0 False (map ppArm arms)
  where ppArm arm =
            sep [pPrint detail 0 (cca_pattern arm) <>
                 ppQuals detail (cca_filters arm) <+> t "-> ",
                 nest 2 (pp detail (cca_consequent arm))]

ppOp :: PDetail -> Int -> Id -> CExpr -> CExpr -> Doc
ppOp d pd i p1 p2 =
        pparen (pd > 0) (sep [pPrint d 1 p1 <> t"" <+> ppInfix d i, pPrint d 1 p2])
{-
        let (p, lp, rp) =
                case getFixity i of
                FInfixl p -> (p, p, p+1)
                FInfixr p -> (p, p+1, p)
                FInfix  p -> (p, p+1, p+1)
        in pparen (d > PDReadable || pd>p)
                  (sep [pPrint d lp p1 <> t"" <+> ppInfix d i, pPrint d rp p2])
-}

ppQuals :: PDetail -> [CQual] -> Doc
ppQuals d [] = t""
ppQuals d qs = t" when" <+> sepList (map (pp d) qs) (t",")

ppOSummands :: PDetail -> [COriginalSummand] -> Doc
ppOSummands d cs = sepList (map (nest 2 . ppOCon) cs) (t" |")
  where ppOCon summand =
            let pp_name = case (cos_names summand) of
                            [cn] -> ppConId d cn
                            cns -> text "(" <>
                                   sepList (map (ppConId d) cns) (text ",") <>
                                   text ")"
                pp_args = map (pPrint d maxPrec) (cos_arg_types summand)
                pp_encoding =
                    case cos_tag_encoding summand of
                    Nothing -> empty
                    Just num ->
                        text "{-# tag " <+> pPrint d 0 num <+> text "#-}"
            in  sep (pp_name : pp_encoding : pp_args)

ppSummands :: PDetail -> [CInternalSummand] -> Doc
ppSummands d cs = sepList (map (nest 2 . ppCon) cs) (t" |")
  where ppCon summand =
            let pp_name = case (cis_names summand) of
                            [cn] -> ppConId d cn
                            cns -> text "(" <>
                                   sepList (map (ppConId d) cns) (text ",") <>
                                   text ")"
                pp_arg = pPrint d maxPrec (cis_arg_type summand)
            in  sep [pp_name, pp_arg]

instance PPrint CDef where
    pPrint d p (CDef  i    ty cs) = ppValueSign d i [] ty cs
    pPrint d p (CDefT i vs ty cs) = ppValueSign d i vs ty cs

instance PPrint CRule where
        pPrint d p (CRule rps mlbl mqs e) =
                ppRPS d rps $+$
                (case mlbl of Nothing -> t""; Just i -> pp d i <> t": ") <> sep [ppQuals d mqs, t "  ==>",
                nest 4 (pp d e)]
        pPrint d p (CRuleNest rps mlbl mqs rs) =
                ppRPS d rps $+$
                (case mlbl of Nothing -> t""; Just i -> pp d i <> t": ") <>
                        (ppQuals d mqs $+$ pBlock d 2 False (map (pp d) rs))

ppRPS :: PDetail -> [RulePragma] -> Doc
ppRPS d [] = text ""
ppRPS d rps = vcat (map (pPrint d 0) rps)

instance PPrint CDefl where
    pPrint d p (CLValueSign def me) = optWhen d me $ pPrint d p def
    pPrint d p (CLValue i cs me) = optWhen d me $
        foldr1 ($+$) (map (\ cl -> ppClause d p [ppVarId d i] cl <> t";") cs)
    pPrint d p (CLMatch pat e) = ppClause d p [] (CClause [pat] [] e)

optWhen :: PDetail -> [CQual] -> Doc -> Doc
optWhen d [] s = s
optWhen d qs s = s $+$ (t"    " <> ppQuals d qs)

ppValueSign :: PDetail -> Id -> [TyVar] -> CQType -> [CClause] -> Doc
ppValueSign d i [] ty cs =
        (ppVarId d i <+> t "::" <+> pp d ty <> t";") $+$
        foldr1 ($+$) (map (\ cl -> ppClause d 0 [ppVarId d i] cl <> t";") cs)
ppValueSign d i vs ty cs =
        (ppVarId d i <+> t ":: /\\" <> sep (map (pPrint d maxPrec) vs) <> t"." <> pp d ty <> t";") $+$
        foldr1 ($+$) (map (\ cl -> ppClause d 0 [ppVarId d i] cl <> t";") cs)

instance PPrint CClause where
    pPrint d p cl = ppClause d p [] cl

ppClause :: PDetail -> Int -> [Doc] -> CClause -> Doc
ppClause d p xs (CClause ps mqs e) =
        sep [sep (xs ++ map (pPrint d maxPrec) ps) <> ppQuals d mqs <+> t "= ",
                  nest 4 (pp d e)]

instance PPrint CQual where
        pPrint d p (CQGen _ pa e) = pp d pa <+> t "<-" <+> pp d e
        pPrint d p (CQFilter e) = pp d e

instance PPrint CPat where
    pPrint d p (CPVar a) = pPrint d p a
    pPrint d p (CPCon i as) = pparen (p>(maxPrec-1)) $ sep (ppConId d i : map (pPrint d maxPrec) as)
    pPrint d p (CPstruct _ tyc []) | tyc == idPrimUnit = text "()"
    pPrint d p (CPstruct _ tyc [(_, fst), (_, snd)]) | tyc == idPrimPair =
        pparen True (pPrint d 0 fst <> t"," <+> pPrint d 0 snd)
    pPrint d p (CPstruct _ i fs) = pparen (p>(maxPrec-1)) $ ppConId d i <+> t "{" <+> sep (map ppField fs ++ [t"}"])
        where ppField (i, CPVar i') | i == i' = ppVarId d i <> t";"
              ppField (i, p) = ppVarId d i <+> t "=" <+> pp d p <> t";"
    pPrint d p (CPAs a pp) = pPrint d maxPrec a <> t"@" <> pPrint d maxPrec pp
    pPrint d p (CPAny _) = text "_"
    pPrint d p (CPLit l) = pPrint d p l
    pPrint d p (CPMixedLit _ base ps) =
        let digitBits = log2 base
            f (len, Just val) = integerFormat (len `div` digitBits) base val
            f (len, Nothing)  = genericReplicate (len `div` digitBits) '?'
            pref  2 = "0b"
            pref  8 = "0o"
            pref 10 = ""
            pref 16 = "0x"
            pref x = internalError ("bad radix to CPMixedLit: " ++ show x)
        in  text (pref base ++ concatMap f ps)
    pPrint d p (CPOper ops) = pparen (p > maxPrec-1) (sep (map (pPrint d (maxPrec-1)) ops))
    pPrint d p (CPCon1 _ i a) = pPrint d p (CPCon i [a])
    ----
    pPrint d p (CPConTs _ i ts as) = pparen (p>(maxPrec-1)) $ sep (ppConId d i : map ppApArg ts ++ map (pPrint d maxPrec) as)
        where ppApArg ty = t"\183" <> pPrint d maxPrec ty

instance PPrint CPOp where
    pPrint d _ (CPRand p) = pp d p
    pPrint d _ (CPRator _ i) = ppInfix d i

ppInfix :: PDetail -> Id -> Doc
ppInfix d i =
    --case getIdString i of
    --s@(c:_) | isIdChar c -> t"`" <> t s <> t"`"
    --s -> t s
    let p = getIdQual i
        b = getIdBase i
    in if (p==fsEmpty) then
              (case getFString b of
               s@(c:_) | isIdChar c -> t"`" <> t s <> t"`"
               s -> t s)
        else (t"`" <> t (getFString p) <> t "." <>
              (case getFString b of
               s@(c:_) | isIdChar c -> t s
               s -> t "(" <> t s <> t")") <> t"`")

instance PPrint CInclude where
    pPrint d p (CInclude s) = pPrint d p s

instance Hyper CPackage where
    hyper x y = (x == x) `seq` y

instance Hyper CDefn where
    hyper x y = (x == x) `seq` y

instance Hyper CClause where
    hyper x y = (x == x) `seq` y
