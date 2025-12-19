{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
module Verilog(
               VArg(..),
               VCaseArm(..),
               VDPI(..),
               VDPIType(..),
               VDType(..),
               VEventExpr(..),
               VExpr(..),
               VFunction(..),
               VId(..),
               VLValue(..),
               VMItem(..),
               VModule(..),
               VOp(..),
               VProgram(..),
               VRange,
               VStmt(..),
               VTri(..),
               VVDecl(..),
               VVar(..),
               VComment,
               vvName,
               vargName,
               commonDeclTypes,
               getVeriInsts,
               vGetMainModName,
               vKeywords,
               vSeq,
               vVDecl,
               vGroup,
               vGroupWithComment,
               mkVId,
               idToVId,
               vidToId,
               getVIdString,
               mkVEOp,
               mkVEUnOp,
               mkEqualsReset, mkNotEqualsReset, mkEdgeReset,
               mkReset, mkNotReset,
               defaultVId,
               vIsValidIdent
--               vVar
              ) where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import Data.List(nub)
import Data.Maybe(fromMaybe)
import Eval
import PPrint
import Fixity(Fixity(..))
import IntegerUtil(integerFormat, aaaa)
import Util(itos, to_quoted_string)
import ErrorUtil(internalError)
import Id
import Position
import FStringCompat
import Data.Char(isDigit, isAlpha)
import qualified Data.Generics as Generic

--import Debug.Trace


-- string to start synthesis attributes with
synthesis_str :: String
synthesis_str = "synopsys"
-- other possibilities
--synthesis_str = "synthesis"
--synthesis_str = "pragma"

mkSynthPragma :: String -> Doc
mkSynthPragma s = text ("// " ++ synthesis_str ++ " " ++ s)


-- VProgram
--    * a list of modules
--    * a list of import-DPI declarations
--    * a comment for the entire file, not for any one module
data VProgram = VProgram [VModule] [VDPI] VComment
        deriving (Eq, Show, Generic.Data, Generic.Typeable)

instance NFData VProgram where
    rnf (VProgram mods dpis cmt) = rnf3 mods dpis cmt

instance NFData VModule where
    rnf (VModule name cmt ports body) = rnf4 name cmt ports body

instance NFData VDPI where
    rnf (VDPI name ret args) = rnf3 name ret args

instance NFData VDPIType where
    rnf VDT_void = ()
    rnf VDT_byte = ()
    rnf VDT_int = ()
    rnf VDT_longint = ()
    rnf (VDT_wide n) = rnf n
    rnf VDT_string = ()
    rnf VDT_poly = ()

instance NFData VId where
    rnf (VId s id mitem) = rnf3 s id mitem

instance NFData VArg where
    rnf (VAInput vid mr) = rnf2 vid mr
    rnf (VAInout vid mvid mmr) = rnf3 vid mvid mmr
    rnf (VAOutput vid mr) = rnf2 vid mr
    rnf (VAParameter vid mr expr) = rnf3 vid mr expr

instance NFData VMItem where
    rnf (VMDecl vdecl) = rnf vdecl
    rnf (VMInst mname iname params ports) = rnf4 mname iname params ports
    rnf (VMAssign lval expr) = rnf2 lval expr
    rnf (VMStmt toff body) = rnf2 toff body
    rnf (VMComment cmt item) = rnf2 cmt item
    rnf (VMRegGroup vid s cmt item) = rnf4 vid s cmt item
    rnf (VMGroup toff body) = rnf2 toff body
    rnf (VMFunction vfun) = rnf vfun

instance NFData VFunction where
    rnf (VFunction name range decls stmt) = rnf4 name range decls stmt

instance NFData VStmt where
    rnf (VAt ev stmt) = rnf2 ev stmt
    rnf (Valways stmt) = rnf stmt
    rnf (Vinitial stmt) = rnf stmt
    rnf (VSeq stmts) = rnf stmts
    rnf (Vcasex expr arms par full) = rnf4 expr arms par full
    rnf (Vcase expr arms par full) = rnf4 expr arms par full
    rnf (VAssign lval expr) = rnf2 lval expr
    rnf (VAssignA lval expr) = rnf2 lval expr
    rnf (Vif expr stmt) = rnf2 expr stmt
    rnf (Vifelse expr s1 s2) = rnf3 expr s1 s2
    rnf (Vdumpvars lvl vars) = rnf2 lvl vars
    rnf (VTask tid exprs) = rnf2 tid exprs
    rnf (VAssert ev exprs) = rnf2 ev exprs
    rnf VZeroDelay = ()

instance NFData VLValue where
    rnf (VLId vid) = rnf vid
    rnf (VLConcat lvals) = rnf lvals
    rnf (VLSub lval expr) = rnf2 lval expr

instance NFData VVDecl where
    rnf (VVDecl dtype mrange vars) = rnf3 dtype mrange vars
    rnf (VVDWire mrange var expr) = rnf3 mrange var expr

instance NFData VExpr where
    rnf (VEConst i) = rnf i
    rnf (VEReal d) = rnf d
    rnf (VEWConst vid w b i) = rnf4 vid w b i
    rnf (VEUnknown w val) = rnf2 w val
    rnf (VEString s) = rnf s
    rnf (VETriConst ts) = rnf ts
    rnf (VEUnOp vid op expr) = rnf3 vid op expr
    rnf (VEOp vid e1 op e2) = rnf4 vid e1 op e2
    rnf (VEVar vid) = rnf vid
    rnf (VEConcat exprs) = rnf exprs
    rnf (VEIndex vid expr) = rnf2 vid expr
    rnf (VESelect e1 e2 e3) = rnf3 e1 e2 e3
    rnf (VESelect1 e1 e2) = rnf2 e1 e2
    rnf (VERepeat e1 e2) = rnf2 e1 e2
    rnf (VEIf e1 e2 e3) = rnf3 e1 e2 e3
    rnf (VEFctCall vid exprs) = rnf2 vid exprs
    rnf (VEMacro s) = rnf s

instance NFData VEventExpr where
    rnf (VEEOr e1 e2) = rnf2 e1 e2
    rnf (VEEposedge expr) = rnf expr
    rnf (VEEnegedge expr) = rnf expr
    rnf (VEE expr) = rnf expr
    rnf (VEEMacro s expr) = rnf2 s expr

instance NFData VCaseArm where
    rnf (VCaseArm exprs stmt) = rnf2 exprs stmt
    rnf (VDefault stmt) = rnf stmt

instance NFData VDType where
    rnf VDReg = ()
    rnf VDWire = ()
    rnf VDInput = ()
    rnf VDInout = ()
    rnf VDOutput = ()

instance NFData VVar where
    rnf (VVar vid) = rnf vid
    rnf (VArray range vid) = rnf2 range vid

instance NFData VTri where
    rnf V0 = ()
    rnf V1 = ()
    rnf Vx = ()
    rnf Vz = ()

instance NFData VOp where
    rnf VNot = ()
    rnf VInv = ()
    rnf VNeg = ()
    rnf VMul = ()
    rnf VQuot = ()
    rnf VRem = ()
    rnf VAdd = ()
    rnf VSub = ()
    rnf VShL = ()
    rnf VShR = ()
    rnf VShLA = ()
    rnf VShRA = ()
    rnf VULT = ()
    rnf VULE = ()
    rnf VUGT = ()
    rnf VUGE = ()
    rnf VEQ = ()
    rnf VNE = ()
    rnf VEQ3 = ()
    rnf VNE3 = ()
    rnf VAnd = ()
    rnf VXor = ()
    rnf VOr = ()
    rnf VLAnd = ()
    rnf VLOr = ()

instance PPrint VProgram where
    pPrint d p (VProgram ms dpis cs) =
        ppComment cs $+$
        assignment_delay_macro $+$
        reset_level_macro $+$
        dpi_decls $+$
        vsepEmptyLine (map (pPrint d 0) ms) $+$
        text ""
      where -- define BSV_ASSIGNMENT_DELAY when the user does not override it
        assignment_delay_macro =
          text "" $+$
          text "`ifdef BSV_ASSIGNMENT_DELAY" $+$
          text "`else" $+$
          text "  `define BSV_ASSIGNMENT_DELAY" $+$
          text "`endif" $+$
          text ""
        reset_level_macro =
          text "`ifdef BSV_POSITIVE_RESET" $+$
          text "  `define BSV_RESET_VALUE 1'b1" $+$
          text "  `define BSV_RESET_EDGE posedge" $+$
          text "`else" $+$
          text "  `define BSV_RESET_VALUE 1'b0" $+$
          text "  `define BSV_RESET_EDGE negedge" $+$
          text "`endif" $+$
          text ""
        dpi_decls =
          vsep (map (pPrint d 0) dpis) $+$
          if (not (null dpis)) then text "" else empty

-- VComment
--    * a list of single-line comments (already broken into lines)
--    XXX perhaps they can be less pre-formatted and pprint can
--    XXX handle wrapping them?
type VComment = [String]

-- return "empty" if there is no comment, which is the unit of $+$,
-- so there is no extra line in the output when there are no comments
ppComment :: [String] -> Doc
ppComment cs =
    let ppline str = text ("// " ++ str)
    in  foldr ($+$) empty (map ppline cs)


-- VDPI
--    * The function name
--    * The return type
--    * The arguments (name, whether it's an input, type)
data VDPI = VDPI VId VDPIType [(VId, Bool, VDPIType)]
        deriving (Eq, Show, Generic.Data, Generic.Typeable)

instance PPrint VDPI where
  pPrint d p (VDPI name ret args) =
    let
        mkDir False = text "output"
        mkDir True  = text "input"
        ppArg (i, dir, t) = mkDir dir <+> pPrint d 0 t <+> pPrint d 0 i
    in
        text "import \"DPI-C\" function" <+>
        pPrint d 0 ret <+> pPrint d 0 name <+> text "(" <>
        sepList (map ppArg args) (text ",") <>
        text ");"

data VDPIType = VDT_void
              | VDT_byte
              | VDT_int
              | VDT_longint
              | VDT_wide Integer
              | VDT_string
              | VDT_poly
        deriving (Eq, Show, Generic.Data, Generic.Typeable)

instance PPrint VDPIType where
  pPrint _ _ VDT_void    = text "void"
  pPrint _ _ VDT_byte    = text "byte unsigned"
  pPrint _ _ VDT_int     = text "int unsigned"
  pPrint _ _ VDT_longint = text "longint unsigned"
  pPrint _ _ (VDT_wide n) = text $ "bit [" ++ itos (n-1) ++ ":0]"
  pPrint _ _ VDT_string  = text "string"
  pPrint _ _ VDT_poly    = text "bit []"


-- VModule:
--    * the module name
--    * a list of single-line comments (already broken into lines)
--    * the ports of the module (possibly grouped and commented)
--    * the internals of the module
data VModule =
    VModule {
             vm_name       :: VId,
             vm_comments   :: VComment,
             vm_ports      ::  [([VArg],VComment)] ,
             vm_body       :: [VMItem]
            }
        deriving (Eq, Show, Generic.Data, Generic.Typeable)

instance PPrint VModule where
    pPrint d p vmodule =
        let
            -- don't include parameters in the port list
            isParam (VAParameter {}) = True
            isParam _ = False
            removeParams = filter (not . isParam)

            comments = ppComment (vm_comments vmodule)
            --
            ports = vm_ports vmodule
            portlist = if null ports
                       then text ""
                       else pparen True $
                            commaSepEmptyLine (map ppPortListGroup ports)

            -- print the comma separated list of port names
            ppPortListGroup :: ([VArg],VComment) -> Doc
            ppPortListGroup ([],_) = empty
            ppPortListGroup (ps,_) =
                -- don't print the comment,
                -- no comma at the end of group (added when combining groups)
                vcatList (map (ppVArgPort d) (removeParams ps)) (text ",")

            -- print the declarations (e.g. "input x;")
            ppPortDeclGroup (ps, comment) =
                let port_decls = ppLinesBy ppVArgDecl d ps
                in  ppComment comment $+$ port_decls

            modheader =
                text "module" <+> pPrint d p (vm_name vmodule)  <>
                portlist <> text ";"
            modbody =
                -- I/O decls and VMItems are indented by two spaces,
                -- and the VMItems have spaces around some items for
                -- readability
                let gs = groupVMItems (vm_body vmodule)
                    ppgroups g = text "  " <> ppLines d g
                in  text "  " <>
                    vsepEmptyLine (map ppPortDeclGroup ports) $+$
                    text "" $+$ -- empty line
                    vsepEmptyLine (map ppgroups gs)
            modtail =
                text "endmodule  //" <+> pPrint d 0 (vm_name vmodule)
        in
            comments $+$ modheader $+$ modbody $+$ modtail


data VArg
        = VAInput VId (Maybe VRange)
        -- If the type is Nothing, then do not print a declaration
        | VAInout VId (Maybe VId) (Maybe (Maybe VRange))
        | VAOutput VId (Maybe VRange)
        | VAParameter VId (Maybe VRange) VExpr
        deriving (Eq, Show, Generic.Data, Generic.Typeable)

-- only use this for debugging
instance PPrint VArg where
    pPrint d p (VAInput i mr) =
        text "VAInput" <+> pPrint d 0 i <+> ppMRange d mr
    pPrint d p (VAInout i Nothing mmr) =
        text "VAInout" <+> pPrint d 0 i <+>
        (case mmr of { Just mr -> ppMRange d mr; Nothing -> empty })
    pPrint d p (VAInout i (Just i') mmr) =
        text "VAInout" <+> pPrint d 0 i <+>
        text "(" <> pPrint d 0 i' <> text ")" <+>
        (case mmr of { Just mr -> ppMRange d mr; Nothing -> empty })
    pPrint d p (VAOutput i mr) =
        text "VAOutput" <+> pPrint d 0 i <+> ppMRange d mr
    pPrint d p (VAParameter i mr e) =
        text "VAParameter" <+> pPrint d 0 i <+> ppMRange d mr <+> pPrint d 0 e

ppVArgPort :: PDetail -> VArg -> Doc
ppVArgPort d (VAInput i _) = pPrint d 0 i
ppVArgPort d (VAInout i Nothing _) = pPrint d 0 i
ppVArgPort d (VAInout i (Just i') _) =
    text "." <> pPrint d 0 i <> text "(" <> pPrint d 0 i' <> text ")"
ppVArgPort d (VAOutput i _) = pPrint d 0 i
ppVArgPort d (VAParameter {}) = empty

ppVArgDecl :: PDetail -> VArg -> Doc
ppVArgDecl d (VAInput vi mr) = pPrint d 0 (VVDecl VDInput mr [VVar vi])
ppVArgDecl d (VAInout vi mvi' (Just mr)) =
    let i = fromMaybe vi mvi'
    in  pPrint d 0 (VVDecl VDInout mr [VVar i])
ppVArgDecl d (VAInout vi mvi' Nothing) = empty
ppVArgDecl d (VAOutput vi mr) = pPrint d 0 (VVDecl VDOutput mr [VVar vi])
ppVArgDecl d (VAParameter i mr e) =
    text "parameter" <+> ppMRange d mr <+> pPrint d 0 i <+>
    text "=" <+> pPrint d 0 e <> text ";"

vargName :: VArg -> VId
vargName (VAInput i _) = i
vargName (VAInout i _ _) = i
vargName (VAOutput i _) = i
vargName (VAParameter i _ _) = i

data VMItem
        = VMDecl VVDecl
        -- VMInst: vmi_instance_params and vmi_instance_ports can be positional
        --         or named, thus the Either (Left = a list of expressions,
        --         by position, and Right = list of (name, expression) pairs)
        | VMInst { vi_module_name :: VId,
                   vi_inst_name :: VId,
                   -- The string is for comments
                   vi_inst_params :: Either [(Maybe String,VExpr)] [(VId, Maybe VExpr)],
                   vi_inst_ports :: [(VId, Maybe VExpr)] }
        | VMAssign VLValue VExpr
        | VMStmt { vi_translate_off :: Bool, vi_body :: VStmt }
        | VMComment VComment VMItem
        -- like VMComment but specific to inlined registers,
        -- to carry info for xref generation.
        -- XXX could this not have been handled in mkRegGroup?
        | VMRegGroup VId String VComment VMItem
        -- VMGroup: the lists of VMItem will be separated by empty lines;
        --          if no spaces needed, use a list of one list.
        | VMGroup { vg_translate_off :: Bool, vg_body :: [[VMItem]]}
        | VMFunction VFunction
        deriving (Eq, Show, Generic.Data, Generic.Typeable)

instance Ord VMItem where
         -- comments are just attached to other statements,
         -- and should not be used for ordering

         compare (VMComment _ x) (VMComment _ y)    = compare x y
         compare (VMComment _ x) y                  = compare x y
         compare x               (VMComment _ y)    = compare x y

         compare (VMRegGroup _ _ _ x) (VMRegGroup _ _ _ y) = compare x y
         compare (VMRegGroup _ _ _ x) y                    = compare x y
         compare x                    (VMRegGroup _ _ _ y) = compare x y

         compare (VMDecl dl) (VMDecl dr)            = compare dl dr
         compare (VMDecl  _) _                      = LT

         compare (VMInst _ _ _ _) (VMDecl _ )       = GT
         compare (VMInst _ _ _ _) (VMInst _ _ _ _)  = EQ
         compare (VMInst _ _ _ _) _                 = LT

         compare (VMAssign vl _) (VMAssign vr _)    = compare vl vr
         compare (VMAssign _ _) (VMDecl _)          = GT
         compare (VMAssign _ _) (VMInst _ _ _ _)    = GT
         compare (VMAssign _ _) _                   = LT

         compare (VMStmt {}) (VMDecl _)              = GT
         compare (VMStmt {}) (VMInst _ _ _ _)        = GT
         compare (VMStmt {}) (VMAssign _ _)          = GT
         compare (VMStmt {}) (VMStmt {})             = EQ
         compare (VMStmt {}) _                       = LT

         compare (VMFunction _) (VMFunction _)      = EQ
         compare (VMFunction _) _                   = GT

         compare (VMGroup _ _) (VMGroup _ _)        = EQ
         compare (VMGroup _ _) _                    = GT


instance PPrint VMItem where
        pPrint d p (VMDecl dcl) = pPrint d p dcl
        pPrint d p s@(VMStmt {})
                | vi_translate_off s = mkSynthPragma "translate_off" $$
                                        pPrint d p (vi_body s) $$
                                        mkSynthPragma "translate_on"
                | otherwise = pPrint d p (vi_body s)
        pPrint d p (VMAssign v e) = -- trace("Assignment :" ++ (ppReadable v) ++ " = " ++ (ppReadable e) ++ "\n") $
            sep [text "assign" <+> pPrint d 45 v <+> text "=",
                      nest 11 (pPrint d 0 e <+> text ";")]
        pPrint d p (VMInst mid iid pvs cs) = pPrint d 0 mid <>
          (case pvs of
           Left ps -> (if null ps then text ""
                       else text " #" <> pparen True (sepList (map (pv95params d) ps) comma ))
           Right ps -> (if null ps then text ""
                        else text " #" <>
                             pparen True (sepList (map (\ (i, me) -> text "." <> pPrint d 0 i <>
                                            pparen True (case me of Just e -> pPrint d 0 e; Nothing -> text "")) ps) (text ",")))) <>
                text "" <+> pPrint d 0 iid <>
                pparen True (sepList (map (\ (i, me) -> text "." <> pPrint d 0 i <>
                                           pparen True (case me of
                                                          Just e -> pPrint d 0 e;
                                                          Nothing -> text "")) cs) (text ","))
                 <> text ";"
        pPrint d p (VMComment cs stmt) = ppComment cs $+$ pPrint d p stmt
        pPrint d p g@(VMGroup _ stmtss)
                | vg_translate_off g = mkSynthPragma "translate_off" $$
                                       vsepEmptyLine (map (ppLines d) stmtss) $$
                                       mkSynthPragma "translate_on"
                | otherwise = vsepEmptyLine (map (ppLines d) stmtss)

        pPrint d p (VMFunction f) = pPrint d p f
        pPrint d p (VMRegGroup inst_id def_name cs stmt) =
            text "// register" <+>
            pPrint d 0 inst_id $+$
            ppComment cs $+$
            pPrint d p stmt

pv95params :: PDetail -> (Maybe String, VExpr) -> Doc
pv95params d (Nothing,x)  =  pPrint d 0 x
pv95params d (Just "", x) =  pPrint d 0 x
pv95params d (Just s,x)   =  text (" /*" ++ s ++ "*/ ") <> pPrint d 0 x

-- Decide where to place blank spaces between VMItems, by grouping
-- them into a list of lists between which there should be a space.
-- A space is added around instantiations and statements (initial and
-- always blocks).
groupVMItems :: [VMItem] -> [[VMItem]]
groupVMItems vmis =
    let
        -- identify which VMItems need a space before and after them
        needsSpace (VMInst _ _ _ _)     = True
        needsSpace (VMStmt _ _)         = True
        needsSpace (VMFunction _)       = True
        needsSpace (VMGroup _ _)        = True
        needsSpace (VMComment _ vmi)    = needsSpace vmi
        needsSpace (VMRegGroup _ _ _ vmi) = needsSpace vmi
        needsSpace _                    = False

        groupNeedsSpace [v] = needsSpace v
        groupNeedsSpace _   = False

        foldFunc v [] = [[v]]
        foldFunc v (g:gs) = if (needsSpace v || groupNeedsSpace g)
                            then ([v]:g:gs)
                            else ((v:g):gs)
    in
        foldr foldFunc [] vmis

-- Convenience function to wrap a list of items in a VMGroup.
-- If the list is empty, return an empty list (don't create a group of nothing)
-- The boolean is whether to add spacing around items in the group
vGroup :: Bool -> [VMItem] -> [VMItem]
vGroup _ [] = []
-- preserve the group, as it implies spacing around the item(s)
--vGroup _ [vmi] = [vmi]
vGroup False vmis = [VMGroup False [vmis]]
vGroup True  vmis = [VMGroup False (groupVMItems vmis)]

-- Convenience function to wrap a list of items in a VMComment of VMGroup.
-- If the list is empty, return an empty list (don't create a group of nothing)
-- The boolean is whether to add spacing around items in the group
vGroupWithComment :: Bool -> [VMItem] -> VComment -> [VMItem]
vGroupWithComment _ [] _ = []
vGroupWithComment False vmis comment = [VMComment comment (VMGroup False [vmis])]
-- Put a blank line not only between lists, but also between the comment and
-- the first list.  To do this, comment an empty group.
vGroupWithComment True  vmis comment =
    let comment_group = [VMComment comment (VMGroup False [])]
        vmi_groups = groupVMItems vmis
    in  [VMGroup False (comment_group : vmi_groups)]


data VFunction = VFunction VId (Maybe VRange) [VFDecl] VStmt
        deriving (Eq, Show, Generic.Data, Generic.Typeable)

type VFDecl = VVDecl -- not quite right

instance PPrint VFunction where
    pPrint d p (VFunction name range decls stmt) =
        (text "function" <+> ppR d range <> pPrint d 0 name <> text ";")
        $+$ (text "  " <> (ppLines d decls))
        $+$ (text "  " <> pPrint d 0 stmt)
        $+$ text "endfunction"
        where ppR _ Nothing = text ""
              ppR d (Just (h,l)) = ppRange d h l <+> text ""

data VStmt
        = VAt VEventExpr VStmt
        | Valways VStmt
        | Vinitial VStmt
        | VSeq [VStmt]
        | Vcasex { vs_case_expr :: VExpr,
                   vs_case_arms :: [VCaseArm],
                   vs_parallel :: Bool,
                   vs_full :: Bool }    -- appears unused
        | Vcase  { vs_case_expr :: VExpr,
                   vs_case_arms :: [VCaseArm],
                   vs_parallel :: Bool,
                   vs_full :: Bool }
        | VAssign VLValue VExpr
        | VAssignA VLValue VExpr
        | Vif VExpr VStmt
        | Vifelse VExpr VStmt VStmt
        | Vdumpvars Int [VId]           -- appears unused
        | VTask VId [VExpr] -- calling a verilog system task as a Bluespec foreign function of type Action
        | VAssert VEventExpr [VExpr]
        | VZeroDelay -- injecting an explicit (0-tick) delay for synchronization purposes
        deriving (Eq, Show, Generic.Data, Generic.Typeable)


instance PPrint VStmt where
        pPrint d p (VAt e s) = sep [text "@" <> pparen True (pPrint d 0 e), pPrint d 0 s]
        pPrint d p (Valways (VAt e s)) = sep [text "always@" <> pparen True (pPrint d 0 e), pPrint d 0 s]
        pPrint d p (Valways s) = sep [text "always", pPrint d 0 s]
        pPrint d p (Vinitial s) =
             text "`ifdef BSV_NO_INITIAL_BLOCKS" $$
             text "`else // not BSV_NO_INITIAL_BLOCKS" $$
             sep [text "initial", pPrint d 0 s] $$
             text "`endif // BSV_NO_INITIAL_BLOCKS"
        pPrint d p (VSeq ss) = text "begin" $+$ (text "  " <> ppLines d ss) $+$ text "end"
        pPrint d p s@(Vcasex {}) =
            (text "casex" <+> pparen True (pPrint d 0 (vs_case_expr s))) <+>
                pprintCaseAttributes (vs_parallel s) (vs_full s) $+$
            (text "  " <> ppLines d (vs_case_arms s)) $+$
            (text "endcase")
        pPrint d p s@(Vcase {}) =
            (text "case" <+> pparen True (pPrint d 0 (vs_case_expr s))) <+>
                pprintCaseAttributes (vs_parallel s) (vs_full s) $+$
            (text "  " <> ppLines d (vs_case_arms s)) $+$
            (text "endcase")
        pPrint d p (VAssign v e) =
            -- if the expr doesn't fit on the same line, indent it 4 spaces
            sep [ pPrint d 0 v <+> text "=",
                  nest 4 (pPrint d 0 e <> text ";") ]
        pPrint d p (VAssignA v e) =
            -- if the expr doesn't fit on the same line, indent it 4 spaces
            sep [ pPrint d 0 v <+> text "<=" <+> text "`BSV_ASSIGNMENT_DELAY",
                  nest 4 (pPrint d 0 e <> text ";") ]
        pPrint d p (Vif e s) | isOne e = pPrint d p s -- optimize ifs that are always true
        pPrint d p (Vif e s) | isZero e = text "" -- optimize away ifs that are always false
        pPrint d p (Vif e s) =
            -- if it doesn't fit on one line, start on the next (indent 2)
            sep [text "if (" <> pPrint d 0 e <> text ")",
                 nest 2 (pPrint d 0 s)]
        pPrint d p (Vifelse e s1 s2) =
            -- for readability, don't allow if-else to fit on one line
            -- (thus, use "vcat" instead of "sep")
            vcat [text "if (" <> pPrint d 0 e <> text ")",
                  nest 2 (pPrint d 0 s1),
                  text "else",
                  nest 2 (pPrint d 0 s2)]
        pPrint d p (Vdumpvars level vars) = text "$dumpvars(" <> sepList dvargs (text ",") <> text ");"
            where dvargs = (pPrint d 0 level):(map (pPrint d 0) vars)
-- no parens when calling a task if it has no arguments
        pPrint d p (VTask task []) | isTaskVId task = pPrint d 0 task <> text ";"
        pPrint d p (VTask task es) = pPrint d 0 task <> text "(" <> commaList d es <> text ");"

        pPrint d p (VAssert ev es) = ppAssert d p ev es


        pPrint d p  VZeroDelay     = text "#0;"

ppAssert :: PDetail -> Int -> VEventExpr -> [VExpr] -> Doc
--ppAssert d i ev (VEString s : es) = text (pretty 78 78 (ppAs1 d i s es))
ppAssert d i ev (VEString s1 :
                 VEString s2 : es) = text (s1++": assert property (@(") <>
                                     pPrint d 0 ev <> text ")" $$
                                     ppAs1 d i s2 es
ppAssert _ _ _ es = internalError ("ppAssert: " ++ show es)

ppAs1 :: PDetail -> Int -> String -> [VExpr] -> Doc
ppAs1 d i s [] = internalError("ppAs1D: " ++ s)
ppAs1 d i "" [b] = text s where
    v0 = ppReadable b
    v = take ((length v0) -1) v0
    s = ") "++v++"=1; else "++v++"=0;"
ppAs1 d i "" es = internalError("ppAs1A: " ++ show es)
ppAs1 d i ('%':'b':s) (x:xs) = pPrint d i x $$ ppAs1 d i s xs
ppAs1 d i ('%':'n':s) (x:xs) = pPrint d i x $$ ppAs1 d i s xs
ppAs1 d i ss@('%':s) (x:xs) = internalError("ppAs1B: " ++ show ss)
ppAs1 d i cs xs = text c1 <> ppAs1 d i c2 xs where
    c1 = takeWhile (/='%') cs
    c2 = dropWhile (/='%') cs

pprintCaseAttributes :: Bool -> Bool -> Doc
pprintCaseAttributes False False = empty
pprintCaseAttributes True  False = mkSynthPragma "parallel_case"
pprintCaseAttributes False True  = mkSynthPragma "full_case"
pprintCaseAttributes True  True  = mkSynthPragma "parallel_case full_case"


-- hack to check if expressions are known to be true or false
isOne :: VExpr -> Bool
isOne (VEConst 1) = True
isOne (VEWConst _ _ _ 1) = True
isOne e = False

isZero :: VExpr -> Bool
isZero (VEConst 0) = True
isZero (VEWConst _ _ _ 0) = True
isZero e = False

data VLValue
        = VLId VId
        | VLConcat [VLValue]
        | VLSub VLValue VExpr
        deriving (Eq, Show, Generic.Data, Generic.Typeable)

instance Ord VLValue where
         compare (VLId lid) (VLId rid)               = compare lid rid
         compare (VLSub vvl _) (VLSub vvr _)         = compare vvl vvr
         compare _ _                                 = EQ

instance PPrint VLValue where
        pPrint d p (VLId i) = pPrint d p i
        pPrint d p (VLConcat vs) = text "{ " <> commaList d vs <> text " }"
        pPrint d p (VLSub i e) = pPrint d 100 i <> text "[" <> pPrint d 0 e <> text "]"

data VCaseArm
        = VCaseArm [VExpr] VStmt
        | VDefault VStmt
        deriving (Eq, Show, Generic.Data, Generic.Typeable)

instance PPrint VCaseArm where
        pPrint d p (VCaseArm es s) =
            -- nest the statement 4 spaces under the expr list
            -- when it doesn't fit on the same line
            sep [ sepList (map (pPrint d 0) es) (text ",") <> text ":",
                  nest 4 (pPrint d 0 s) ]
        pPrint d p (VDefault s) = text "default:" <+> pPrint d 0 s

-- Always add begin end blocks -- more consistent with a "good" Verilog style
vSeq :: [VStmt] -> VStmt
-- vSeq [s] = s
vSeq ss = VSeq ss

data VVDecl
        = VVDecl VDType (Maybe VRange) [VVar]
        | VVDWire (Maybe VRange) VVar VExpr
        deriving (Eq, Show, Generic.Data, Generic.Typeable)

instance Ord VVDecl where
         compare (VVDecl _ _ _)  (VVDWire _ _ _)       = LT
         compare (VVDWire _ _ _) (VVDecl _ _ _)        = GT
         compare (VVDecl tl mrl vvl) (VVDecl tr mrr vvr)= compare (tl,mrr,vvl) (tr,mrl,vvr) -- vars with range are first, the mmr mrl swap is not a typo
         compare (VVDWire mrl vl _) (VVDWire mrr vr _)  = compare vl vr

instance PPrint VVDecl where
        pPrint d p (VVDecl t (Just (h, l)) is) =
            pPrint d p t <+> ppRange d h l <+> commaList d is <> text ";"
        pPrint d p (VVDecl t Nothing is) =
            pPrint d p t <+> commaList d is <> text ";"

        pPrint d p (VVDWire (Just (h, l)) i e) =
            sep [text "wire" <+> ppRange d h l <+> pPrint d 0 i <+> text "=",
                      nest 4 (pPrint d 0 e <> text ";")]
        pPrint d p (VVDWire Nothing i e) =
            sep [text "wire" <+> pPrint d 0 i <+> text "=",
                      nest 4 (pPrint d 0 e <> text ";")]

-- A short cut constructor
vVDecl :: VDType -> Maybe VRange -> VVar -> VVDecl
vVDecl t r v = VVDecl t r [v]



data VDType = VDReg | VDWire
        | VDInput | VDInout | VDOutput                -- only for decls
        deriving (Eq, Ord, Show, Generic.Data, Generic.Typeable, Enum)

instance PPrint VDType where
        pPrint d p VDReg    = text "reg"
        pPrint d p VDWire   = text "wire"
        pPrint d p VDInput  = text "input "
        pPrint d p VDInout  = text "inout "
        pPrint d p VDOutput = text "output"

data VVar
        = VVar VId
        | VArray VRange VId
        deriving (Eq, Show, Generic.Data, Generic.Typeable)

instance Ord VVar where
         compare (VVar lid) (VArray _ rid)           = compare lid rid
         compare (VArray _ lid) (VVar rid)           = compare lid rid
         compare (VVar lid) (VVar rid)               = compare lid rid
         compare (VArray lr lid) (VArray rr rid)     = compare lid rid

instance PPrint VVar where
        pPrint d p (VVar i) = pPrint d p i
        pPrint d p (VArray (l, h) i) = pPrint d p i <> ppRange d l h

vvName :: VVar -> VId
vvName (VVar i) = i
vvName (VArray _ i) = i


-- the VMItem is used for inlined registers
data VId = VId String Id (Maybe VMItem)
        deriving (Show, Generic.Data, Generic.Typeable)

instance Ord VId where
    compare (VId s1 _ _) (VId s2 _ _) = compare s1 s2

instance Eq VId where
    VId string _ _ == VId string' _ _ = (string == string')

mkVId :: String -> VId
mkVId string = VId string
                   (mkId noPosition
                         (mkFString string))
                Nothing

idToVId :: Id -> VId
idToVId id = (VId (getIdString id) id Nothing)

vidToId :: VId -> Id
vidToId (VId _ i _) = i

getVIdString :: VId -> String
getVIdString (VId s _ _) = s

instance PPrint VId where
        pPrint d p (VId s i _) = text s

instance HasPosition VId where
  getPosition (VId _ inside_id _) = getPosition inside_id

-- whether a VId is syntactically a task ID
isTaskVId :: VId -> Bool
isTaskVId (VId ('$':_) _ _) = True
isTaskVId _ = False


type VRange = (VExpr, VExpr)

data VEventExpr
        = VEEOr VEventExpr VEventExpr
        | VEEposedge VExpr
        | VEEnegedge VExpr
        | VEE VExpr
        | VEEMacro String VExpr
        deriving (Eq, Show, Generic.Data, Generic.Typeable)

instance PPrint VEventExpr where
        pPrint d p (VEEOr e1 e2) =
            -- if the second expr doesn't fit on the same line,
            -- put it on the next line
            sep [pPrint d 10 e1 <+> text "or",
                 pPrint d 10 e2]
        pPrint d p (VEEposedge e) = text "posedge" <+> pPrint d 10 e
        pPrint d p (VEEnegedge e) = text "negedge" <+> pPrint d 10 e
        pPrint d p (VEE e) = pPrint d p e
        pPrint d p (VEEMacro s e) = text ("`" ++ s) <+> pPrint d (p+1) e


data VExpr
        = VEConst Integer
        | VEReal Double
        | VEWConst VId Integer Integer Integer -- width base value  (what is VId?)
        | VEUnknown Integer String
        | VEString String
        | VETriConst [VTri]
        | VEUnOp VId VOp VExpr
        | VEOp VId VExpr VOp VExpr
        | VEVar VId
        | VEConcat [VExpr]
        | VEIndex VId VExpr
        | VESelect VExpr VExpr VExpr
        | VESelect1 VExpr VExpr
        | VERepeat VExpr VExpr
        | VEIf VExpr VExpr VExpr
        | VEFctCall VId [VExpr]
        | VEMacro String
        deriving (Eq, Ord, Show, Generic.Data, Generic.Typeable)

-- vVar :: String -> VExpr
-- vVar = VEVar . VId

instance PPrint VExpr where
        pPrint d p (VEConst i) = text (itos i)
        pPrint d p (VEReal r) = text (show r)
        pPrint d p v@(VEWConst _ w b i) = text (createVEWConstString w b i)

--        pPrint d p (VEUnknown w) = text (itos w ++"'b0/*x*/")
        pPrint d p (VEUnknown w val) = pPrint d p v <> text " /* unspecified value */ "
            where wint = fromInteger w
                  v = case val of
                        "A" -> (VEWConst (mkVId (itos (aaaa w)))
                                         w 2 (aaaa w))
                        "0" ->  (VEWConst (mkVId (itos (0::Integer)))
                                         w 2 (0))
                        "1" ->  VETriConst (replicate wint V1)
                        "X" ->  VETriConst (replicate wint Vx)
                        "Z" ->  VETriConst (replicate wint Vz)
                        _   ->  internalError( "Verilog::pPrint: " ++ ppReadable val)
        pPrint d p (VEString s) = text $ to_quoted_string s
        pPrint d p (VEMacro s)  = text ("`" ++ s)
        pPrint d p (VETriConst ts) = text (itos (length ts) ++ "'b") <> foldr (<>) (text "") (map (pPrint d 0) ts)
        pPrint d p (VEUnOp _ op e) = pparen (p>11) (pPrint d 0 op <> pPrint d 100 e)
        pPrint d p (VEOp vid e1 op e2) = ppOp d p vid e1 op e2
        pPrint d p (VEVar i) = pPrint d p i
        pPrint d p (VEConcat es) = text "{ " <> commaList d es <> text " }"
        pPrint d p (VEIndex i e) = pPrint d 100 i <> text "[" <> pPrint d 0 e <> text "]"
        pPrint d p (VESelect e h l) = pPrint d 100 e <> text "[" <> pPrint d 0 h <> text ":" <> pPrint d 0 l <> text "]"
        pPrint d p (VESelect1 e pos) = pPrint d 100 e <> text "[" <> pPrint d 0 pos <> text "]"
        pPrint d p (VERepeat e1 e2) | isZero e1 = internalError ("Verilog.pPrint - bad VERepeat: " ++ ppReadable (e1, e2))
        pPrint d p (VERepeat e1 e2) = text "{" <> pPrint d 100 e1 <> text "{" <> pPrint d 0 e2 <> text "}}"

        -- possibly redundant but the Vif analog helps optimize foreign function calls
        pPrint d p (VEIf e1 e2 e3) | isOne e1 = pPrint d p e2  -- optimize conditional expressions known to be true
        pPrint d p (VEIf e1 e2 e3) | isZero e1 = pPrint d p e3 -- optimize conditional expressions known to be false

        pPrint d p (VEIf e1 e2 e3) =
            pparen (p > 0)  $ sep [ pPrint d 100 e1 <+> text "?", nest 2 (pPrint d 1 e2 <+> text ":"), nest 2 (pPrint d 1 e3) ]
        pPrint d p (VEFctCall f []) | isTaskVId f = pPrint d 0 f
        pPrint d p (VEFctCall f es) = pPrint d 0 f <> text "(" <> commaList d es <> text ")"

createVEWConstString :: Integer -> Integer -> Integer -> String
createVEWConstString width base 0 =
    (itos width ++ "'" ++ baseChar base ++ "0")
        where baseChar :: Integer -> String
              baseChar  2 = "b"
              baseChar  8 = "o"
              baseChar 10 = "d"
              baseChar 16 = "h"
              baseChar  _ = "b"
createVEWConstString width base value =
    (itos width ++ "'" ++ baseChar base' ++ integerFormat width' base' value)
        where baseChar :: Integer -> String
              baseChar  2 = "b"
              baseChar  8 = "o"
              baseChar 10 = "d"
              baseChar 16 = "h"
              baseChar  b =
                  internalError ("baseChar: unexpected pattern: " ++ show b)

              whichBase :: Integer -> Integer -> Integer
              whichBase 0 i = whichBase 16 i
              whichBase _ i | i > 2000000000 = 16
              whichBase b _ = fromInteger b
              whichWidth 2 w = w
              whichWidth 8 w = (w+2) `div` 3
              whichWidth 10 w = 0
              whichWidth 16 w = (w+3) `div` 4
              whichWidth w _ = internalError ("whichWidth: unexpected pattern: " ++ show w )

              base' = whichBase base value
              width' = whichWidth base' width

data VTri = V0 | V1 | Vx | Vz
        deriving (Eq, Ord, Show, Generic.Data, Generic.Typeable, Enum)

instance PPrint VTri where
        pPrint d p V0 = text "0"
        pPrint d p V1 = text "1"
        pPrint d p Vx = text "x"
        pPrint d p Vz = text "z"


data VOp
        = VNot                          -- logical not !
        | VInv                          -- bit wise inverse
        | VNeg
        | VMul | VQuot | VRem
        | VAdd | VSub
        | VShL | VShR
        | VShLA | VShRA
        | VULT | VULE | VUGT | VUGE
        | VEQ | VNE | VEQ3 | VNE3
        | VAnd                          -- bitwise Operations
        | VXor
        | VOr
        | VLAnd                         -- logical AND and OR
        | VLOr
        deriving (Eq, Ord, Show, Generic.Data, Generic.Typeable, Enum)


instance PPrint VOp where
        pPrint d p op = text (getOpString op)

getOpString :: VOp -> String
getOpString VNot = "!"
getOpString VInv = "~"

getOpString VNeg = "-"

getOpString VMul  = "*"
getOpString VQuot = "/"
getOpString VRem  = "%"

getOpString VAdd = "+"
getOpString VSub = "-"

getOpString VShL = "<<"
getOpString VShR = ">>"
getOpString VShRA = ">>>"
getOpString VShLA = "<<<"

getOpString VULT  = "<"
getOpString VULE  = "<="
getOpString VUGE  = ">="
getOpString VUGT  = ">"

getOpString VEQ  = "=="
getOpString VNE  = "!="
getOpString VEQ3 = "==="
getOpString VNE3 = "!=="

getOpString VAnd = "&"

getOpString VXor  = "^"

getOpString VOr  = "|"

getOpString VLAnd = "&&"

getOpString VLOr = "||"


getOpFixity :: VOp -> Fixity
getOpFixity op =
    case op of
        VNot -> FInfix  15
        VInv -> FInfix  15

        VNeg -> FInfix  13

        VMul -> FInfixl 11
        VQuot -> FInfixl 11
        VRem -> FInfixl 11

        VAdd -> FInfixa 10
        VSub -> FInfixl 10

        VShL -> FInfix  9
        VShR -> FInfix  9
        VShLA -> FInfix  9
        VShRA -> FInfix  9

        VULT -> FInfix  8
        VULE -> FInfix  8
        VUGE -> FInfix  8
        VUGT -> FInfix  8

        VEQ  -> FInfix  7
        VNE  -> FInfix  7
        VEQ3 -> FInfix 7
        VNE3 -> FInfix 7

        VAnd -> FInfixa 6

        VXor -> FInfixa 5

        VOr  -> FInfixa 4

        VLAnd-> FInfixa 3

        VLOr -> FInfixa 2

--        _ -> internalError ("getOpFixity " ++ show op)

-- Only keep assoc for for Sub.  Keep VAdd out of this list, since DC can
-- do a better job with optimization without parens Bug 302
keepAssoc :: VOp -> Bool
keepAssoc op = op `elem` [VSub{-,  VAdd, VAnd, VOr, VXor-}]

vGetMainModName :: VProgram -> String
vGetMainModName (VProgram program_items _ _) =
        let get_mod_name (headmod:_) = getVIdString $ vm_name headmod
            get_mod_name [] = internalError "vGetMainModName: no main module"
        in  get_mod_name program_items


vKeywords :: [String]
vKeywords =
    [
    "or", "rtran", "nor", "assign", "realtime", "tran", "not", "endcase", "endtable", "endmodule",
    "table", "endfunction", "endprimitive", "for", "nand", "force", "forever", "deassign", "event",
    "repeat", "end", "output", "posedge", "function", "parameter", "endspecify", "default", "and",
    "case", "casez", "specify", "wor", "strong0", "rtranif0", "else", "release", "notif0", "tranif0",
    "buf", "real", "large", "negedge", "scalered", "wand", "strong1", "rtranif1", "begin", "notif1",
    "tranif1", "edge", "trior", "integer", "vectored", "join", "rnmos", "inout", "bufif0", "supply0",
    "xor", "xnor", "weak0", "nmos", "disable", "task", "triand", "pulldown", "if", "always", "endtask",
    "primitive", "input", "bufif1", "supply1", "fork", "weak1", "rpmos", "module", "wire", "while",
    "specparam", "pmos", "rcmos", "reg", "tri0", "defparam", "pullup", "wait", "casex", "cmos",
    "macromodule", "tri1", "pull0", "trireg", "small", "tri", "signed", "pull1", "time", "highz0",
    "localparam", "medium", "highz1", "initial"
    ]

vIsValidIdent :: String -> Bool
vIsValidIdent ""     = False
vIsValidIdent (c:cs) = (isLetterOrUnderscore c) &&
                       all isLetterDigitUnderscoreOrDollar cs
  where isLetterOrUnderscore x = (isAlpha x) || (x == '_')
        isLetterDigitUnderscoreOrDollar x =
            (isAlpha x) || (isDigit x) || (x == '_') || (x == '$')

-------

ppLines :: PPrint a => PDetail -> [a] -> Doc
ppLines d xs = foldr ($+$) empty (map (pPrint d 0) xs)

ppLinesBy :: (a -> b -> Doc) -> a -> [b] -> Doc
ppLinesBy f d xs = foldr ($+$) empty (map (f d) xs)

vsepEmptyLine :: [Doc] -> Doc
vsepEmptyLine [] = empty
vsepEmptyLine xs = foldr1 (\x y -> x $+$ text "" $+$ y) xs

commaList :: PPrint a => PDetail -> [a] -> Doc
commaList d xs = sepList (map (pPrint d 0) xs) (text ",")

{-
-- commaList uses sep, which can put things on one line
vcatCommaList :: PPrint a => PDetail -> [a] -> Doc
vcatCommaList d xs = vcatList (map (pPrint d 0) xs) (text ",")
-}

-- both of the above functions at once
commaSepEmptyLine :: [Doc] -> Doc
commaSepEmptyLine [] = empty
commaSepEmptyLine xs = foldr1 (nextLine) xs
    where nextLine :: Doc -> Doc -> Doc
          nextLine x y
              | (x == empty) && (y == empty) = empty
              | (x == empty)                 = y
              | (y == empty)                 = x
              | otherwise                    =  x <> text "," $+$ text "" $+$ y

ppRange :: PDetail -> VExpr -> VExpr -> Doc
ppRange d a b = text "[" <> pPrint d 0 a <+> text ":" <+> pPrint d 0 b <> text "]"

ppMRange :: PDetail -> Maybe VRange -> Doc
ppMRange _ Nothing = empty
ppMRange d (Just (h,l)) = ppRange d h l

ppOp :: PDetail -> Int -> VId -> VExpr -> VOp -> VExpr -> Doc

ppOp d pd vid@(VId string id _) p1 op p2 =
        let (p, lp, rp) =
                case getOpFixity op of
                FInfixl p -> (p, p,   p+1)
                FInfixr p -> (p, p+1, p)
                FInfix  p -> (p, p+1, p+1)
                FInfixa p -> (p, p,   p)
                FPrefix   -> (p, p,   p )
        in pparen (d > PDReadable || pd>p || pd==p && keepAssoc op)
                  (sep [pPrint d lp p1 <> text"" <+> pPrint d 0 op, pPrint d rp p2])


-------

getVeriInsts :: VProgram -> [String]
getVeriInsts (VProgram ms _ _) = nub (concatMap getInstsFromVModule ms)
  where
      getInstsFromVModule vmod = concatMap getInstsFromVMItem (vm_body vmod)
      -- extract module names from instances in VMItem
      getInstsFromVMItem (VMInst { vi_module_name = vid }) = [getVIdString vid]
      getInstsFromVMItem (VMComment _ i) = getInstsFromVMItem i
      getInstsFromVMItem (VMRegGroup _ _ _ i) = getInstsFromVMItem i
      getInstsFromVMItem (VMGroup _ iss) =
          concatMap (concatMap getInstsFromVMItem) iss
      getInstsFromVMItem _ = []

-- true if the declarions have the same type
commonDeclTypes :: VVDecl -> VVDecl -> Bool
commonDeclTypes (VVDecl t1 r1 _ ) (VVDecl t2 r2 _ )     = (t1,r1) == (t2,r2)
commonDeclTypes _ _                                     = False

-- #############################################################################
-- #
-- #############################################################################

mkVEOp :: VExpr -> VOp -> VExpr -> VExpr
mkVEOp vexpr_0 vop vexpr_1 = VEOp defaultVId vexpr_0 vop vexpr_1

mkVEUnOp :: VOp -> VExpr -> VExpr
mkVEUnOp vop vexpr = VEUnOp defaultVId vop vexpr

defaultVId :: VId
defaultVId = mkVId "Default"


-- #############################################################################
-- #
-- #############################################################################

mkEqualsReset :: VExpr -> VExpr
mkEqualsReset e = mkVEOp e VEQ mkReset

mkNotEqualsReset :: VExpr -> VExpr
mkNotEqualsReset e = mkVEOp e VNE mkReset


mkEdgeReset :: VExpr -> VEventExpr
mkEdgeReset e = VEEMacro "BSV_RESET_EDGE" e

mkReset :: VExpr
mkReset =  VEMacro "BSV_RESET_VALUE"

mkNotReset :: VExpr
mkNotReset = mkVEUnOp VNot mkReset
