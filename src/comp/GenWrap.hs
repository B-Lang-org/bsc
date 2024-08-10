{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fwarn-name-shadowing #-}
module GenWrap(
               genWrap,
               WrapInfo(..)
              ) where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import Data.List(nub, (\\), find, genericLength)
import Control.Monad(when, foldM, filterM, zipWithM, mapAndUnzipM)
import Control.Monad.Except(ExceptT, runExceptT, throwError)
import Control.Monad.State(StateT, runStateT, lift, gets, get, put)
import PFPrint
import Position(Position, noPosition, getPositionLine, cmdPosition)
import Error(internalError, EMsg, EMsgs(..), ErrMsg(..), ErrorHandle, bsError)
import ErrorMonad(ErrorMonad, convErrorMonadToIO)
import Flags(Flags)
import FStringCompat
import PreStrings(fsUnderscore, fs_t, fsTo, fsFrom, fsEmpty, fsEnable, fs_rdy)
import Id
import IdPrint
import PreIds
import CSyntax
import CSyntaxUtil
import SymTab(SymTab, TypeInfo(..), FieldInfo(..), findType, addTypesUQ,
              findField, findFieldInfo, getMethodArgNames)
import MakeSymTab(convCQType)
import Pred hiding (name)
import qualified Pred(name)
import Scheme
import Assump
import CType(cTNum, cTStr, tyConArgs, getArrows, cTVarNum, isIfc, getRes, typeclassId)
import VModInfo(VSchedInfo, VPathInfo(..), VeriPortProp(..), VArgInfo(..),
                VFieldInfo(..), VName(..), VWireInfo(..), VPort)
-- GenWrap defines its own versions that expand synonyms and use qualEq
import Type hiding (isPrimAction, isActionValue, getAVType,
                    isReset, isClock, isInout)
import TypeCheck(cCtxReduceDef)
import Subst(mkSubst, Types(..))
import Classic(isClassic)
import Pragma
import PragmaCheck
import Data.Maybe
import Util
import qualified Data.Map as M
import GenWrapUtils

-- ====================

type GWMonad = StateT GenState (ExceptT EMsgs IO)

data GenState = GenState
 {
   errHandle  ::  ErrorHandle,
   symtable   ::  SymTab,
   flags      ::  Flags
 }

runGWMonad :: GWMonad a -> GenState -> IO a
runGWMonad f s = do
  let errh = errHandle s
  result <- runExceptT ((runStateT f) s)
  case result of
    Right (res, _) -> return res
    Left msgs -> bsError errh (errmsgs msgs)

-- don't expect it to fail
runGWMonadNoFail :: GWMonad a -> GenState -> IO a
runGWMonadNoFail f s =
    do (_, res) <- runGWMonadGetNoFail f s
       return res

-- get the state as well,
-- and we don't expect it to fail
runGWMonadGetNoFail :: GWMonad a -> GenState -> IO (GenState, a)
runGWMonadGetNoFail f s =
    do result <- runExceptT ((runStateT f) s)
       case result of
         Right (res, s2) -> return (s2, res)
         Left msgs -> internalError ("runGWMonadGetNoFail: " ++
                                     ppReadable (errmsgs msgs))

-- for converting from ErrorMonad
convEM :: ErrorMonad a -> GWMonad a
convEM m = do
  errh <- gets errHandle
  lift $ lift $ convErrorMonadToIO errh m

getFlags :: GWMonad Flags
getFlags = gets flags

getSymTab :: GWMonad SymTab
getSymTab = do s <- get
               return (symtable s)

newSymTab :: SymTab -> GWMonad ()
newSymTab symtnew = do s <- get
                       put (s { symtable = symtnew })

bad :: EMsg -> GWMonad a
bad msg = throwError (EMsgs [msg])

bads :: [EMsg] -> GWMonad a
bads msgs = throwError (EMsgs msgs)

-- ====================

-- Field types   can these be nested ?
-- Yes fields can be other interfaces
data FInf = FInf
 {
   name :: Id,
   arg_types :: [CType],
   ret_type :: CType,
   -- a list of any user-provided names (empty if no names)
   arg_names :: [Id]
 }
 deriving (Eq, Show)

instance PPrint FInf where
    pPrint d p finf =
        text "FInf: " <+>
        ppId d (name finf) <+>
        pPrint d p (arg_types finf) <+>
        pPrint d p (ret_type finf) <+>
        pPrint d p (arg_names finf)

instance (HasPosition) FInf where
  getPosition finf = getPosition (name finf)

-- ====================

type DefFun = Bool -> VWireInfo -> VSchedInfo -> VPathInfo ->
              [VPort] -> SymTab -> [VFieldInfo] -> [Id] ->
              IO CDefn

data WrapInfo = WrapInfo
 {
   mod_nm      :: Id,           -- module name for synthesis eg mkTest
   orig_cqt    :: CQType,       -- cqtype of original module
   wrapper_ifc :: Id,           -- munged interface name
   wrapped_mod :: Id,           -- Id of wrapped module eg.  mkTest_
   wi_prags    :: [PProp],
   deffun      :: DefFun
 }

instance PPrint WrapInfo where
    pPrint d p wi@(WrapInfo id1 cqt id2 id3 ps _) =
       text "WrapInfo:" <+> ppId d id1 <> text(" :: ") <> pPrint d 0 cqt <>
       text(" id2: ") <>  ppId d id2 <> text(" id3: ") <>
       ppId d id3 $+$
       text(" PProps: ")
       <> sepList ( map (pPrint d p) ps) (text ",")

-- ====================

-- A shallow processing of the interface of a synthesized module (or of an
-- import-BVI).  It lists the original type, it's original field names, and
-- any applicable attributes from the module (such as "always_enabled")
-- and it adds to that some shallow information about the flattened ifc
-- type which will be created later: the name of that type, a list of names
-- of the numeric type arguments that it takes, and a mapping from types in
-- original ifc to their bitified forms in the new ifc (using type names
-- from the argument name list).

-- Until we support synthesis of size-parameterized modules, the argument
-- list and type map will be empty for synthesized modules.  Only import-BVI
-- modules will have non-empty lists.

data IfcTRec = IfcTRec
  {
    rec_id        :: Id,        -- name of the flattened ifc ("<ifc>_")
    rec_rootid    :: Id,        -- type constructor of the original type
    rec_isforeign :: Bool,      -- whether it is from an import-BVI
    rec_type      :: CType,     -- the original ifc type
    rec_pprops    :: [PProp],   -- module properties which apply to the ifc
    rec_kind      :: Kind,      -- kind of the flattened ifc
                                -- (can be derived from the numArgs)
    rec_finfs     :: [FInf],    -- fields of the original ifc
                                -- with _unqualified_ names
    rec_numargs   :: [Id],             -- names of the numeric type args
                                       -- of the flattened ifc
    rec_typemap   :: [(CType, CType)]  -- mapping from types in the orig ifc
                                       -- to their form in the flattened ifc
  }
  deriving (Eq, Show)

instance PPrint IfcTRec where
    pPrint d p r =
        text "IfcTRec:" <+> ppId d (rec_id r) <+> equals <+>
        braces (
                (if (rec_isforeign r) then text "(Foreign)" else empty) <+>
                text "rootid:" <> pPrint d p (rec_rootid r) $+$
                text "type:" <> pPrint d p (rec_type r) $+$
                text "pprops:" <> pPrint d p (rec_pprops r) $+$
                pPrint d p (rec_kind r) $+$
                pPrint d p (rec_finfs r) $+$
                pPrint d p (rec_numargs r) <+>
                pPrint d p (rec_typemap r)
               )

-- ====================

-- Information about a flattened, bitified interface

-- The IfcTRec information is further processed (along with the symtab)
-- to create this information.

data GeneratedIfc = GeneratedIfc
    {
     genifc_id     :: Id,
     genifc_kind   :: Kind,
     genifc_cdefn  :: CDefn,
     genifc_pprops :: [PProp]
    }
  deriving (Show)

instance PPrint GeneratedIfc where
    pPrint d p gifc =
        text "GeneratedIfc: " <+> ppId d (genifc_id gifc) <+> equals <+>
             braces (
                      pPrint d p (genifc_cdefn gifc)
                      $+$ pPrint d p (genifc_pprops gifc)
                    )

-- ====================

-- Info about modules to be synthesized
-- This data is passed between the stages of "genWrapE"

type ModDefInfo = (CDef, CQType,  -- the new "<mod>_" def and it's type
                   [(Id, CType, ArgInfo)], -- mod arg info with user names
                   [PProp])  -- pprops on the module

-- ====================
-- Top-level entry: genWrap

-- creates wrappers for separately compiled modules: wraps pack/unpack around method
-- arguments and results; surfaces method ready signals
-- Pragma are module specific
genWrap :: ErrorHandle -> Flags -> [String] -> Bool -> CPackage -> SymTab ->
           IO (CPackage, [WrapInfo])
genWrap errh flgs genNames generating cpack symt = do
    runGWMonad (genWrapE generating ppmap cpack) origstate
 where
    origstate = GenState errh symt flgs
    pragmas = (extractPragmas cpack)
    ppmap = makePPropMap genNames pragmas
    --
    extractPragmas :: CPackage -> [Pragma]
    extractPragmas (CPackage _ _ _ _ ds _) = [ p | CPragma p <- ds ]

-- ====================

-- Given a list of names to generate from the command line (with -g flag)
-- and the pragmas from the CPackage, generate a mapping from def names
-- to their associated pprops (removing any duplicate pprops)
makePPropMap :: [String] -> [Pragma] -> M.Map Id [PProp]
makePPropMap genNames cpragmas =
    let
        -- We avoid adding cmd-line pragmas that duplicate source pragmas,
        -- but we don't "nub" the source pragmas and we don't use "union"
        -- to construct the map, because we want to preserve the order of
        -- "doc" attributes, which don't have to be unique, either.
        cmd_line_pragmas = makeCmdLineGenPragmas genNames
        all_pragmas = (cmd_line_pragmas \\ cpragmas) ++ cpragmas
        pairs = [ (i, pps) | (Pproperties i pps) <- all_pragmas ]
    in  M.fromListWith (++) pairs

makeCmdLineGenPragmas :: [String] -> [Pragma]
makeCmdLineGenPragmas genNames =
    let
        -- Turn a string into a qualitifed id with cmdPosition
        mId :: String  -> Id
        mId s =
            case span (/= '.') s of
                (ms, '.':is) ->
                    let fms = mkFString ms
                        fis = mkFString is
                    in  mkQId cmdPosition fms fis
                _ ->
                    let fs = mkFString s
                    in  mkId cmdPosition fs
    in  [ Pproperties (mId i)  [PPverilog] | i <- genNames ]

isGenDef :: M.Map Id [PProp] -> Id -> Bool
isGenDef pmap i =
    case (M.lookup i pmap) of
      Just pps -> PPverilog `elem` pps
      Nothing -> False

-- ====================

-- A new interface is created in the CSyntax, which has the name <Top>_.  This interface
--   extends the existing one by adding the ready and enable signals
--   Only modules which have the verilog/synthesis pragma are "wrapped"

genWrapE :: Bool -> M.Map Id [PProp] -> CPackage ->
            GWMonad (CPackage, [WrapInfo])
genWrapE generating ppmap cpack@(CPackage packageId exps imps fixs ds includes)  =
    do
       -- information on all modules which are being generated
       -- (this checks the pragmas on all defs which have pragmas, though,
       -- and errors if any do not meet sanity checks)
       -- moduledefs :: [(CDef, CQType, [(Id, CType, ArgInfo)], [PProp])]
       moduledefs <- concatMapM (getDef generating ds) (M.toList ppmap)
       --traceM( "genWrapE:  moduledefs: " ++ ppReadable moduledefs )

       -- build the Interface record
       -- this structure should be used throughout
       -- ifcTypeRecords :: [IfcTRec]
       ifcTypeRecords <- mapM procDef moduledefs
       let trs0 = concat ifcTypeRecords
       let trs = nub trs0

       -- create the type records for Verilog interfaces
       (defsWithVector, trs') <- foldM fixVerilogIfc ([],[]) ds
       let finalIfcTRecs = nub (trs0 ++ reverse trs')
       --traceM( "IfcTRec: " ++ ppReadable finalIfcTRecs )

       -- New interface is generated here
       -- let newFlatIfcs :: [(Id, Kind, [FInf], CDefn), [PProp]]
       newFlatIfcs <- mapM genTDef finalIfcTRecs
       let genIfcMap = M.fromList $ map (\g -> (genifc_id g, g)) newFlatIfcs

       --traceM ( "genWrapE moduledefs :" ++ ppReadable moduledefs )
       --traceM ( "genWrapE ifcTypeRecords : " ++ ppReadable ifcTypeRecords)
       ----traceM ( "genWrapE old dis_tmp :" ++ ppReadable dis_tmp )
       --traceM ( "genWrapE old record :" ++ ppReadable finalIfcTRecs )
       --traceM ( "genWrapE new ifc :" ++ ppReadable newFlatIfcs )

       -- Update the symbol table for newFlatIfcs
       symt <- getSymTab
       let symt' = foldr (extSym packageId) symt newFlatIfcs
       newSymTab symt'

       -- The following make up the new definition list in the CPackage.
       let ifcdefns = map genifc_cdefn newFlatIfcs  -- new interface definitions

       -- create new new module definitions for the CPackage
       newModule_s <- mapM (mkNewModDef genIfcMap) moduledefs

       to_Defs <- mapM mkTo_ trs
       from_Defs <- mapM mkFrom_ trs
       let ifcConversionDefs = to_Defs ++ from_Defs

       let fixedDefs = map fixDef defsWithVector

       instanceDefs <- concatMapM mkInstances trs
       -- XXX we don't update the symbol table with the new instances
       -- XXX we rely on the symbol table being rebuilt

       let finalDefs = reverse fixedDefs ++
                       ifcdefns ++
                       newModule_s ++
                       ifcConversionDefs ++
                       instanceDefs

       gens <- mapM (genWrapInfo newFlatIfcs) moduledefs

       --traceM ( "gen wrap: wrapinfo : " ++ ppReadable gens )
       ----traceM ( "gen Wrap: dis : " ++ ppReadable dis )
       ----traceM ( "gen wrap: ifcds : " ++ ppReadable ifcds )
       --traceM ( "gen wrap: ds_ : " ++ ppReadable newModule_s )
       --traceM ( "gen wrap: to_s : " ++ ppReadable ifcConversionDefs )
       return (
           CPackage packageId exps imps fixs finalDefs includes,
           gens
          )
    where
       -- Adds the new types into the symbol table
       extSym :: Id -> GeneratedIfc -> SymTab -> SymTab
       extSym mid genifc symt =
           -- include both the qualified and unqualified names
           addTypesUQ symt [(qdi, tyinf), (di, tyinf)]
         where
           di    = genifc_id genifc
           qdi   = qualId mid di
           k     = genifc_kind genifc
           -- the type only has parameters if it's a wrapped foreign func
           -- (in which case, the params are sizes from added Bits provisos)
           -- XXX should we give better names in that case?
           vs    = []
           -- XXX if we need the field names, get them from genifc_cdefn
           ti    = TIstruct (SInterface noIfcPragmas)
                       (internalError "extSym: tried to access field names")
           tyinf = TypeInfo (Just qdi) k vs ti

       -- removes the [CClause] from the input, and replaces it with singleton list
       fixDef :: CDefn -> CDefn
       fixDef (CValueSign (CDef defid t e)) | generating &&
                                              isGenDef ppmap defid =
           CValueSign (CDef defid t [CClause [] [] (CVar defid)])
       fixDef d = d


-- --------------------
-- genWrapE toplevel: procDef

-- This takes the ModDefInfo (computed by getDef) for each module to be
-- synthesized and returns a IfcTRec for each flattened interface that
-- needs to be created.  It returns a list because it used to support
-- interface arguments, so it would return the provided interface plus
-- any given interfaces.  (Probably only returns one element lists now.)

-- XXX note that it doesn't do a full recursive sweep of the interface

-- Check all definition types and put them in a convenient form
-- XXX the work here is forgotten and repeated many times throughout GenWrap
procDef :: ModDefInfo -> GWMonad [IfcTRec]
procDef (def@(CDef _ t _), _, _, pps) =
    do --traceM( "procdef : def= " ++ ppReadable def ) ;
       ts <- chkType def t
       res <- mapM (makeIfcTRec pps) ts
       return res
procDef _ = internalError "genWrapE::procDef not CDef"

-- check that the type being generated is legal (uses the def to get a position)
chkType :: CDef -> CQType -> GWMonad [CType]
chkType def ty =
 do
   let defId = getDName def
   symt <- getSymTab
   case convCQType symt ty of
     Left msg -> bad msg
     Right ((_:_) :=> _) ->
        let ctx = if isClassic() then "context" else "proviso"
            msg = "It has a " ++ ctx ++ "."
        in  bad (getPosition def, EBadIfcType (pfpString defId) msg)
     Right ([]    :=> t) ->
      do
        if not (null (tv t))
          then let msg = "Its interface is polymorphic."
               in  bad (getPosition def, EBadIfcType (pfpString defId) msg)
          else
           do
             --traceM ("chkType: " ++ pfpReadable (t, getArrows t))
             case getArrows t of
               (args, TAp (TCon (TyCon tm _ _)) tr) | tm == idModule -> do
                  pint <- getPolyInterface tr
                  case pint of
                    -- XXX: should do better with the exact field position
                    (f:_) -> let msg = "Its interface has a polymorphic field " ++
                                       quote (pfpString f) ++ "."
                             in  bad (getPosition def,
                                      EBadIfcType (pfpString defId) msg)
                    [] ->
                     do
                       ----traceM ("chkType 2: " ++ pfpReadable (chkInterface tr))
                       cint <- chkInterface tr
                       case cint of
                         Just _ ->
                          do
                            trs <- getInterfaces args
                            return (tr : trs)
                         Nothing -> let msg = "The type " ++
                                              quote (pfpString t) ++
                                              " is not an interface."
                                    in  bad (getPosition def,
                                             EBadIfcType (pfpString defId) msg)
               _ -> let msg = "It is not a module."
                    in  bad (getPosition def,
                             EBadIfcType (pfpString defId) msg)

-- Return a list of names of any fields which are polymorphic,
-- if the given type is an interface; otherwise return an empty list.
getPolyInterface :: Type -> GWMonad [Id]
getPolyInterface t = do
  t' <- expandSynSym t
  case (leftCon t') of
    Nothing -> return []
    Just i -> do
      let ts = tyConArgs t'
      symt <- getSymTab
      case findType symt i of
        Just (TypeInfo (Just ti) _ _ (TIstruct ss fs)) | isIfc ss -> do
          res <- filterM (isPolyFieldType ti ts) fs
          return res
        _ -> return []


-- Build the Interface record
makeIfcTRec :: [PProp] -> Type -> GWMonad IfcTRec
makeIfcTRec pps t =
    do res <- chkInterface t
       let pps' = filter isRelevantProp pps
       case res of
         Nothing -> internalError ("makeIfcTRec: not interface - " ++ show t)
         Just (_, _, fts) ->
           do -- name based on module attributes not ifc attributes
              flat_t <- flatTypeId pps' t
              raw <- rawTypeId t
              let rootId = addInternalProp raw
              --
              return IfcTRec { rec_id        = flat_t,
                               rec_isforeign = False,
                               rec_rootid    = rootId,
                               rec_type      = t,
                               rec_pprops    = pps',
                               rec_kind      = KStar,
                               rec_finfs     = fts,
                               rec_numargs   = [],
                               rec_typemap   = [] }

-- pulls out all PProps relevant to GenWrap
isRelevantProp :: PProp -> Bool
isRelevantProp (PPalwaysReady {})      = True
isRelevantProp (PPalwaysEnabled {})    = True
isRelevantProp (PPenabledWhenReady {}) = True
isRelevantProp _                       = False


-- --------------------
-- genWrapE toplevel: getDef

-- For each definition which has PProps attached to it, this checks
-- the properties, and then for those which are to be generated
-- (that the property PPverilog) it creates a record of information:
-- * The def (possibly updated with a new type if it is to be generated,
--   because polymorphic modules get tied to Module)
-- * The original CQType (before tying down the polymorphic module type)
--   for use on the wrapper around the Verilog
-- * Triples of the names of the module arguments and their types,
--   along with a breakdown of the argument (for Vector arguments)
-- * The list of PProps
getDef :: Bool -> [CDefn] -> (Id, [PProp]) -> GWMonad [ModDefInfo]
getDef generating ds (i, pps) =
 do
   flgs <- getFlags
   symt <- getSymTab
   let defs = [ d | d@(CValueSign (CDef i' _ _)) <- ds, unQualId i == unQualId i' ]
   case defs of
     [d] -> do                  -- single element list of the module definition
        let red = cCtxReduceDef flgs symt d
        case red of
          Left msgs -> bads msgs
          Right (CValueSign (CDef defid cqt@(CQType ctx t) e)) ->
            do
              t_ext <- expandSynSym t
              let ext = (CQType ctx t_ext)
              let vts = getDefArgs e t_ext
              vtis <- mapM expandArg vts
              let pps' = renamePProps vtis pps
              -- check pragmas for every def
              convEM $ checkModuleArgPragmas (getPosition i) pps pps' vtis
              -- only return info for the defs which are generated
              if (generating && (PPverilog `elem` pps'))
                then do newtyp <- fixupPolyModType ext
                        return [(CDef defid newtyp e,
                                 cqt, vtis, pps')]
                else return []
          Right _ -> internalError ("genWrapE::getDef unexpected CtxReduce def" ++ show d )
     _ -> bad (getIdPosition i, EUnboundVar (pfpString i))
 where
   expandArg :: (Id, CType) -> GWMonad (Id, CType, ArgInfo)
   expandArg (v_orig, vt_orig) = do
     let expandInfo :: Id -> CType -> GWMonad ArgInfo
         expandInfo v vt = do
             isVector <- isVectorType vt
             case isVector of
                 Just (n,tVec, isListN) -> expandVecInfo v n tVec isListN
                 _ -> return (Simple v vt)
         expandVecInfo :: Id -> Integer -> Type -> Bool -> GWMonad ArgInfo
         expandVecInfo v sz tVec isListN = do
             -- name the ports p_0, p_1, ...
             let mkSuffix n = concatFString [fsUnderscore, mkFString (itos n)]
                 mkNewName n = mkIdPost v (mkSuffix n)
                 new_vs = map mkNewName [0..(sz-1)]
             -- see if the underlying type is itself a vector
             sub_infos <- mapM (`expandInfo` tVec) new_vs
             return (Vector isListN v tVec sub_infos)
     info <- expandInfo v_orig vt_orig
     return (v_orig, vt_orig, info)


-- force IsModule to be Module when we are generating
fixupPolyModType :: CQType -> GWMonad CQType
fixupPolyModType ty =
 do
   symt <- getSymTab
   case convCQType symt ty of
     Left msg -> return ty -- let other processing handle the error
     -- note that any other provisos will be an error while generating anyway
     Right ([pp] :=> t) ->
       case (removePredPositions pp) of
         (IsIn cls [TVar tv1, TVar tv2]) | (typeclassId (Pred.name cls) == idIsModule)
           -> do
                let modSubst = mkSubst [(tv1, tModule), (tv2, tId)]
                return (CQType [] (apSub modSubst t))
         _ -> return ty
     _ -> return ty


-- --------------------
-- genWrapE toplevel: genWrapInfo

-- This takes the ModDefInfo (computed by getDef) for each module to be
-- synthesized and generates the WrapInfo structure which is returned
-- from GenWrap (info about the module and a DefFun continuation which is
-- used at the end of synthesis to make the final wrapper).
-- It also takes the list of generated interfaces, in which it will find
-- the info for the interface of the current module.

-- User pragmas are checked that any names match the actual flattened ifc.
-- Pragmas on the ifc type declaration are added to the module's list of
-- pragmas (returned in the WrapInfo).

genWrapInfo :: [GeneratedIfc] -> ModDefInfo -> GWMonad WrapInfo
genWrapInfo genifcs (d@(CDef modName oqt@(CQType _ t) cls), cqt, _, pps) =
 do
   ifcName_ <- ifcNameFromMod pps t
   -- lookup the generate ifc for this module
   let mifc = find (qualEq ifcName_ . genifc_id) genifcs
       err = internalError ( "genWrapInfo:: cannot find interface " ++
                             ppReadable ifcName_ ++ ppReadable genifcs )
       ifc = maybe err id mifc
   let iprops = genifc_pprops ifc
   chkUserPragmas pps ifc
   -- XXX the new module name should be already created in ModDefInfo,
   -- XXX so that it does not have to be created both here and in mkNewModDef
   let newModName = modIdRename pps modName
   --traceM ("genWrapInfo" ++ ppReadable ifcName_ ++ ppReadable newModName)
   --traceM ("genWrapInfo" ++ ppReadable genifcs)
   namefun <- mkDef iprops pps d cqt -- pass down the pragma for the wrapper gen state
   return WrapInfo { mod_nm      = modName,
                     orig_cqt    = oqt,
                     wrapper_ifc = ifcName_,
                     wrapped_mod = newModName,
                     wi_prags    = (pps ++ iprops),-- combine pragmas
                     deffun      = namefun }
 where
   --Get interface name from module XXX make disappear
   -- XXX this was already done, but we did not keep the name !
   ifcNameFromMod :: [PProp] -> Type -> GWMonad Id
   ifcNameFromMod localpps localt = flatTypeIdQual localpps tr
     where
       tr = case getArrows localt of
              (_, TAp _ r) -> r
              _ -> internalError "GenWrap.genWrapInfo ifcNameFromMod: tr"
genWrapInfo _ (def,_,_,_) =
    internalError( "genWrapInfo: unexpected def: " ++ ppReadable def )


-- --------------------
-- genWrapE toplevel: fixVerilogIfc

-- BSV import-BVI statements have an implied wrapper which converts between
-- the bitified signals and the abstract values.  This function looks for
-- import-BVI constructs and inserts the wrapper, also returning an IfcTRec
-- for each new flattended ifc that needs to be declared.

-- finds definitions containing CmoduleVerilog bodies, and alters the
-- name of their interface types to the "derived id":
-- (*A*) Note: this matches syntax generated in CVParserImperative: see
-- the comment labelled (*A*) in CVParserImperative.lhs
-- This looks for CModuleVerilog definition (import BVI), and creates  the new definition and
-- IfcTRec for it.
fixVerilogIfc :: ([CDefn], [IfcTRec]) -> CDefn -> GWMonad ([CDefn], [IfcTRec])
fixVerilogIfc (ds,ts) x@(CValueSign (CDef n (CQType prs tid) [CClause ps qs (Cmodule pos body)])) =
 do
    (newBody, tyrs, prs') <- foldM (fixCModuleVerilog n) ([],[],prs) body
    let d'= (CValueSign (CDef n (CQType prs' tid) [CClause ps qs (Cmodule pos (reverse newBody))]))
    --
    return (d':ds, tyrs++ts)

fixVerilogIfc (ds,ts) d = return ((d:ds),ts)


-- a fix for vectors of interfaces
fixCModuleVerilog :: Id -> ([CMStmt], [IfcTRec], [CPred]) -> CMStmt -> GWMonad ([CMStmt], [IfcTRec], [CPred])
fixCModuleVerilog n (ss,ts,ps)
       bdy@(CMStmt (CSBindT p@(CPVar mName) mi pprops cq@(CQType qs ty)
                            def@(CApply _ [CmoduleVerilog _ _ _ _ aes fs _ _]))) = do
   let mStmtSPT = savePortTypeStmt (CVar id_x)
       mStmtSPTO = savePortTypeOfStmt (CVar id_x)
   let saveArgTypes (Port vp _ _, e) = [mStmtSPTO vp e]
       saveArgTypes (InoutArg vn _ _,
                     CApply (CVar f) [e]) | f == idPrimInoutCast0 =
         let vp = (vn,[])
         in  [mStmtSPTO vp e]
       saveArgTypes _ = []
   let saveFieldTypes finf (Method { vf_inputs = inps,
                                     vf_output = mo }) = do
         let rt = ret_type finf
         isAV <- isActionValue rt
         output_type <- if isAV then getAVType "fixCModVer" rt else return rt
         let output_stmt = maybeToList (fmap ((flip mStmtSPT) rt) mo)
         -- we let the type-checker error on mismatches
         return (output_stmt ++ (zipWith mStmtSPT inps (arg_types finf)))
       saveFieldTypes finf (Inout { vf_inout = vn }) = do
         let rt = ret_type finf
             vp = (vn,[])
         return [mStmtSPT vp rt]
       saveFieldTypes _ _ = return []

   cint <- chkInterface ty
   rawid <- rawTypeId ty
   let rootId = addInternalProp rawid

   case cint of
    Nothing -> bad (getPosition cq, EBadForeignIfcType (pfpString ty))
    Just (i, k, fts) ->
     do
       -- XXX This flattening is redone in genIfcFieldFN
       -- XXX We should flatten once -- maybe by storing the flattened FInfs?
       let flattenFInfs prefixes (FInf f as r aIds) = do
               mifc <- chkInterface r
               case (mifc, as) of
                 (Just (_, _, finfs), []) -> do
                     newPrefixes <- extendPrefixes prefixes [] r f
                     meths <- mapM (flattenFInfs newPrefixes) finfs
                     return (concat meths)
                 _ -> -- if Vector of ifcs was supported,
                      -- we'd have to handle it here
                      return [FInf (binId prefixes f) as r aIds]
       flat_fts <- concatMapM (flattenFInfs noPrefixes) fts

       let finf_map = M.fromList [(unQualId (name finf), finf) | finf <- flat_fts]
       let save_f f =
               let fname = vf_name f
               in  -- imports don't have RDY methods
                   if (isRdyId fname)
                   then return []
                   else case (M.lookup fname finf_map) of
                          Just finf -> saveFieldTypes finf f
                          Nothing -> bad (getIdPosition fname,
                                          EForeignModNotField
                                              (pfpString i) (pfpString fname))
       save_f_stmtss <- mapM save_f fs
       let save_a_stmtss = map saveArgTypes aes
       let save_stmts = concat (save_a_stmtss ++ save_f_stmtss)
       let pos = getPosition n
           ftypes = nub (concatMap (\ (FInf fid as r aIds) -> (r:as)) flat_fts)
       (_, numArgs', actualArgs', fieldTypes, ps')
           <- foldM procType (0,[],[],[],[]) (reverse ftypes)
       let actualArgs  = reverse actualArgs'
           numArgs     = reverse numArgs'
           newLeftId   = setInternal $
                         enumId (getIdString i) pos (getPositionLine(pos))
           newLeftKind = foldr (\ a lk -> Kfun KNum lk) KStar actualArgs
           newLeftSort = TIstruct (SInterface noIfcPragmas) (internalError "procType: tried to access field names")
           newLeftType = TCon (TyCon newLeftId (Just newLeftKind) newLeftSort)
           newType = cTApplys newLeftType actualArgs
           no_rdys = map (\v -> [vf_name v]) (filter (not . (hasReadyFN fs)) fs)
           rdyPPs = case no_rdys of
             [] -> []
             _ -> [PPalwaysReady no_rdys] -- No ready signals for clocks, resets, etc
           s' =(CMStmt
                 (CSBindT p mi pprops
                   (CQType qs newType) def))
           tr' = IfcTRec { rec_id        = newLeftId,
                           rec_isforeign = True,
                           rec_rootid    = rootId,
                           rec_type      = ty,
                           rec_pprops    = rdyPPs,
                           rec_kind      = newLeftKind,
                           rec_finfs     = fts,
                           rec_numargs   = numArgs,
                           rec_typemap   = fieldTypes }
           -- saving port types has to be after the instantiation
           -- and saving its name
           ss' = save_stmts ++ ((saveNameStmt mName id_x):s':ss)
       return (ss', tr':ts, ps' ++ ps)
fixCModuleVerilog n (ss, ts, ps) s = return (s:ss, ts, ps)


procType ::
    (Int, [Id], [CType], [(CType, CType)], [CPred]) -> CType ->
    GWMonad (
      Int,  -- next unique num for creating numeric type arg Ids
      [Id], -- names of the numeric types created so far (of the form "n_#")
            -- as used in the type map below (collected in reverse order)
      [CType], -- numeric type variables created so far (of the form "sn_#")
               -- as used in the provisos below (collected in reverse order)
      [(CType, CType)],
            -- map from types in the original ifc to their bitified form
            -- (using "n_#" sizes)
      [CPred] -- Bits provisos which convert the original types to the
              -- numeric types "sn_#"
    )
procType (n, ns, as, ts, ctx) ty = do
  let hasVars t = not (null (tv t))
      newSVar = cTVarNum (enumId "sn" noPosition n)
      newId  = enumId "n" noPosition n
      cBit t = cTApplys tBit [t]
      cInout_ t = cTApplys tInout_ [t]
      bitsCtx a s = CPred (CTypeclass idBits) [a, s]
  isAV <- isActionValue ty
  if isAV then do
    av_t <- getAVType "procType" ty
    return (n+1, newId:ns, newSVar:as,
            (ty, (TAp tActionValue_  (cTVarNum newId))):ts,
            (bitsCtx av_t newSVar):ctx)
   else do
     isInout <- isInoutType ty
     case isInout of
       Just t ->
         if hasVars t then
              return (n+1, newId:ns, newSVar:as,
                      (ty, cInout_ (cTVarNum newId)):ts,
                      (bitsCtx t newSVar):ctx)
         else return (n, ns, as, ts, ctx)
       Nothing ->
         if hasVars ty then
              return (n+1, newId:ns, newSVar:as,
                      (ty, cBit (cTVarNum newId)):ts,
                      (bitsCtx ty newSVar):ctx)
         else return (n, ns, as, ts, ctx)


-- --------------------
-- genWrapE toplevel: genTDef

-- Given a IfcTRec structure for the ifc of a synthesized module,
-- produce the
-- Generate a new interface with Id and CDefn
-- Any interface hierarchy is flattened,  leaving a new interface
genTDef :: IfcTRec -> GWMonad GeneratedIfc
genTDef trec@(IfcTRec newId rootId _ sty _ k fts args _) =
 do
   -- generate the new interfaces
   (ifc',newprops) <- genIfc trec args k
   --traceM( "genTDef: ifc " ++ ppReadable ifc' )
   --traceM( "genTDef:: new prop are: " ++ ppReadable newprops )
   return GeneratedIfc {
      genifc_id = newId,
      genifc_kind = k,
      genifc_cdefn = ifc',
      genifc_pprops = newprops }

-- Generate a new interface definition for the CPackage
-- Basically, this consists of a Cstruct of sub-type Sintrface.
-- The fields are generated in genIfcField
-- accomplished by traversing down the possibly nested interface definitions
-- The props are ones extracted from the ifc, and must be propagated to the module
genIfc :: IfcTRec -> [Id] -> Kind -> GWMonad (CDefn, [PProp] )
genIfc trec args knd =
    do let fts    = rec_finfs trec
           rootId = rec_rootid trec
           si     = rec_id trec
       --traceM("genIfc: " ++ ppReadable trec ) ;
       -- lookup interface pragmas from symt and pass them in.
       iprags <- getInterfacePrags rootId
       let prefix = noPrefixes { ifcp_pragmas = iprags }
       fieldprops <- mapM (genIfcField' trec rootId prefix ) fts
       let (fields,ppropss) = unzip fieldprops
       let newprops = concat ppropss
       --
       return ( (Cstruct True (SInterface iprags) (IdKind si knd) args ( (concat fields)) []),
                newprops )
    where
    genIfcField' = if rec_isforeign trec
                    then genIfcFieldFN -- foreign module case
                    else genIfcField

-- Generate the ifc fields
-- And any new AR AE pragmas from the methods
-- Note: The FInf are assumed to have unqualified field names.
genIfcField :: IfcTRec -> Id -> IfcPrefixes -> FInf -> GWMonad ([CField], [PProp] )
genIfcField trec ifcIdIn prefixes (FInf fieldIdQ argtypes rettype _) =
    do
       -- get relevant pragmas for this interface and field
       --traceM( "prefixes for: " ++ ppReadable fieldId ++ " = " ++ ppReadable prefixes )
       -- looking up the pragmas requires the qualified name
       ciPrags <- getInterfaceFieldPrags ifcIdIn fieldIdQ
       -- but for the rest of the work, we only need the unqualified name
       let fieldId = unQualId fieldIdQ
       --traceM( "prags for field are: " ++ ppReadable fieldId ++ " = " ++ ppReadable ciPrags)
       --
       mi <- chkInterface rettype
       case mi of
           Just (ifcId, k, fts) | null argtypes ->  -- recursive function this is an ifc of ifc
             do -- create new prefixes before creating new sub-interface fields
                newPrefixes <- extendPrefixes prefixes ciPrags rettype fieldId
                --
                -- if the field is an interface, use its interface Id to
                -- recurse and look up field information
                fieldsprops <- mapM (genIfcField trec ifcId newPrefixes ) fts
                let (fields,props) = unzip fieldsprops
                return ((concat fields), (concat props))
           _ ->               -- leaf function
             do
              isClock <- isClockType rettype
              isReset <- isResetType rettype
              isInout <- isInoutType rettype
              let isIot = isInout/=Nothing
              isPA <- isPrimAction rettype
              isVec <- isVectorInterfaces rettype
              case (isVec, argtypes) of
                (Just (n, tVec, isListN), []) ->
                    do -- Vectors of interfaces are interfaces
                       --traceM ("tVec:" ++ (show tVec))
                       let nums = map mkNumId [0..(n-1)]
                       newPrefixes <- extendPrefixes prefixes ciPrags rettype fieldId
                       let recurse num = genIfcField trec ifcIdIn newPrefixes  (FInf num [] tVec [])
                       fieldsprops <- mapM recurse nums
                       let (fields,props) = unzip fieldsprops
                       return (concat fields, concat props)
                _ -> do  -- ELSE NOT a Vec
                      let v = cTVar $ head tmpTyVarIds
                      let ctx = CPred (CTypeclass idWrapMethod) [foldr arrow rettype argtypes, v]

                      let fi = binId prefixes fieldId
                      --
                      let (mprops, ifcPragmas) = gen prefixes ciPrags fieldId fi
                          gen | isClock   = genNewClockIfcPragmas
                              | isReset   = genNewResetIfcPragmas
                              | isIot     = genNewInoutIfcPragmas
                              | otherwise = genNewMethodIfcPragmas

                      let ifc_field = CField { cf_name = fi,
                                              cf_pragmas = Just ifcPragmas,
                                              cf_type = CQType [ctx] v,
                                              cf_orig_type = Just (foldr arrow rettype argtypes),
                                              cf_default = []
                                            }
                      --
                      -- the ready field
                      let rdy_field = if (isClock || isReset || isIot) then []
                                      else mkReadyField trec ifcPragmas ifcIdIn fieldId fi
                      --
                      --traceM( "ifc_fields is: " ++ ppReadable ifc_field)
                      return ((ifc_field : rdy_field), mprops )


-- create a RDY field, if requested
mkReadyField :: IfcTRec -> [IfcPragma] -> Id -> Id -> Id -> [CField]
mkReadyField trec ifcprags rootIfcId fieldId pathFieldId = if makingReady then [cfield] else []
    where  pps = rec_pprops trec
           readyId = mkRdyId pathFieldId -- why mkRdyId only to compare it later?
           makingReady = not ((isAlwaysRdy pps readyId) || (isAlwaysReadyIfc ifcprags) )
           --
           renamed = mkRdyId pathFieldId
           cfield = CField { cf_name = renamed,
                             cf_pragmas = Nothing,
                             cf_type = (CQType [] (TAp tBit (cTNum 1 (getPosition fieldId)))),
                             cf_orig_type = Nothing,
                             cf_default = []
                           }

-- The same (as genIfcField) but for foreign modules.
-- Note: The FInf are assumed to have unqualified field names.
genIfcFieldFN :: IfcTRec -> Id  -> IfcPrefixes -> FInf -> GWMonad ( [CField], [PProp])
genIfcFieldFN trec rootId  prefixes (FInf fieldIdQ argtypes r _) =
 do
   let typeMap = rec_typemap trec
   -- looking up the pragmas requires the qualified name
   ciPrags <- getInterfaceFieldPrags rootId fieldIdQ
   -- but for the rest of the work, we only need the unqualified name
   let fieldId = unQualId fieldIdQ
   mi <- chkInterface r
   case mi of
     Just (ifcId, k, fts) | null argtypes ->  -- recursive function this is an ifc of ifc
           do -- create new prefixes before creating new sub-interface fields
             newPrefixes <- extendPrefixes prefixes ciPrags r fieldId
             --
             -- if the field is an interface, use its interface Id to recurse and look up field information
             fieldsprops <- mapM (genIfcFieldFN trec ifcId newPrefixes ) fts
             let (fields,props) = unzip fieldsprops
             return ((concat fields), (concat props))


     Just _ ->   -- recursive interface def
             internalError ( "genIfcFieldFN -- invalid hierarchy of interfaces" )

     Nothing ->            -- leaf function
      do
        symt <- getSymTab
        let (v, vs) = unconsOrErr "GenWrap.genIfcFieldFN: v:vs" $
                        map cTVarNum (take (length argtypes + 1) tmpTyVarIds)
            isTClock t = t == tClock
            isTReset t = t == tReset
            isTInout t = (leftCon t == Just idInout)
            bitsCtx a s = CPred (CTypeclass idBits) [a, s]
            newTypeCtx t lctx lv =
                case lookup t typeMap of
                  Just t' -> (t', lctx)
                  Nothing ->
                      let newTCtx
                            | isTClock t                       = (t,lctx)
                            | isTReset t                       = (t,lctx)
                            | leftCon t == Just idBit          = (t,lctx)
                            | leftCon t == Just idActionValue_ = (t,lctx)
                            | leftCon t == Just idActionValue  = (t,lctx)
                            | isTInout t                       =
                                let it = headOrErr "inout arg" (tyConArgs t)
                                in  (TAp tInout_ lv, bitsCtx it lv : lctx)
                            | otherwise                        =
                                (TAp tBit lv, bitsCtx t lv : lctx)
                      in newTCtx
            fldfn (t,lv) (largtypes,lctx) =
                let (t',ctx') = newTypeCtx t lctx lv
                in  (t':largtypes, ctx')
            (newAs,ctx) = foldr fldfn ([],[]) (zip argtypes vs)

        isPA <- isPrimAction r
        isClock <- isClockType r
        isReset <- isResetType r
        isInout <- isInoutType r
        let isIot = isInout/=Nothing

        let (r', ctx') = if (isPA || isClock || isReset) then (r, ctx)
                         else newTypeCtx r ctx v
        let fi = binId prefixes fieldId

        ----traceM ("Making readyFN for " ++ (ppReadable fi) ++ " of " ++ (show pps) ++ ": " ++ (show makingReady))
        let (mprops,ifcPragmas) = gen prefixes [] fieldId fi
            gen | isClock   = genNewClockIfcPragmas
                | isReset   = genNewResetIfcPragmas
                | isIot     = genNewInoutIfcPragmas
                | otherwise = genNewMethodIfcPragmas

        let ifc_field = CField { cf_name = fi, cf_pragmas = Just ifcPragmas,
                                 cf_type = CQType ctx' (foldr arrow r' newAs),
                                 -- probably unnecessary, but can't hurt
                                 -- import "BVI" is tracked differently
                                 cf_orig_type = Just $ foldr arrow r argtypes,
                                 cf_default = []
                               }
        let rdy_field = mkReadyField trec ifcPragmas rootId fieldId fi

        ----traceM (pfpReadable ((fieldId, t), (argtypes, r), ctx))
        return ((ifc_field : rdy_field),
                mprops )


-- --------------------
-- genWrapE toplevel: mkTo_

-- For an interface, make the function which converts from the original
-- interface type to the flattened interface type

-- (the underscore is because traditionally the flattened version of an
-- interface "X" was named "X_", though now we are more sophisticated about
-- generating different flattened types from the same original type, based
-- on differing attributes)

mkTo_ :: IfcTRec -> GWMonad CDefn
mkTo_ trec@(IfcTRec { rec_numargs = [], rec_typemap = [] }) =
 do
   let pps = rec_pprops trec
       -- i = rec_id trec
       t = rec_type trec
   tyId <- flatTypeId pps t
   let arg = id_t (getPosition t)
   let ty = t `fn` cTCon tyId
   to <- (genTo pps t (CVar arg))
   let cls = CClause [CPVar arg] [] to
   return (CValueSign (CDef (to_Id tyId) (CQType [] ty) [cls]))
mkTo_ x = internalError "GenWrap::mkTo_ "

-- Create the name of the function which converts to the given interface
to_Id :: Id -> Id
to_Id i = addInternalProp (mkIdPre fsTo i)


genTo :: [PProp] -> CType -> CExpr -> GWMonad CExpr
genTo pps ty mk =
 do
   --traceM ("genTo type: " ++ (pfpAll ty))
   cint <- chkInterface ty
   case cint of
     Nothing -> internalError ("genTo: " ++ pfpReadable (ty, mk))
     Just (_, _, fts) -> do
       meths <- mapM (meth mk noPrefixes) fts
       fty <- flatTypeId pps ty
       let tmpl = Cinterface (getPosition fts) (Just fty) (concat meths)
       return tmpl
 where
   meth :: CExpr -> IfcPrefixes -> FInf -> GWMonad [CDefl]
   meth sel prefixes (FInf f as r aIds) =
    do
       mi <- chkInterface r
       case (mi, as) of
         (Just (_, _, fts), []) -> do
           isAV <- isActionValue r
           if isAV
             then internalError "genTo 2: unexpected AV"
             else do
               --traceM ("selector: " ++ show sel)
               newPrefixes <- extendPrefixes prefixes [] r f
               meths <- mapM (meth (extSel sel f) newPrefixes) fts
               return (concat meths)
         _ ->  do  -- Generate the Verilog template for X
           isVec <- isVectorInterfaces r
           case (isVec, as) of
             (Just (vn, tVec, _), []) -> do
               --traceM ("toVec:" ++ (show tVec))
               let nums = [0..(vn-1)] :: [Integer]
               let primselect = idPrimSelectFn noPosition
               let lit k = CLit $ num_to_cliteral_at noPosition k
               let selector n = cVApply primselect [posLiteral noPosition, extSel sel f, lit n]
               elemPrefix <- extendPrefixes prefixes [] r f
               let recurse num = do
                                    numPrefix <- extendPrefixes elemPrefix [] r (mkNumId num)
                                    meth (selector num) numPrefix (FInf idEmpty [] tVec [])
               fields <- mapM recurse nums
               return (concat fields)
             _ -> do
               -- XXX idEmpty is a horrible way to know no more selection is required
               let arg_names = mkList
                    [stringLiteralAt (getPosition i) (getIdString i)
                    | i <- aIds ++ map mkNumId [genericLength aIds + 1..genericLength as]]
               let ec = if f == idEmpty then sel else CSelect sel (setInternal f)
               let e = CApply (CVar id_toWrapMethod) [arg_names, ec]
               return [CLValue (binId prefixes f) [CClause [] [] e] []]

-- --------------------
-- genWrapE toplevel: mkFrom_

-- XXX this duplicates the traversals done by mkTo_ / genIfcField
mkFrom_ :: IfcTRec -> GWMonad CDefn
mkFrom_ trec@(IfcTRec { rec_numargs = [], rec_typemap = [] }) =
 do
   let pps = rec_pprops trec
       -- i = rec_id trec
       t = rec_type trec
   tyId <- flatTypeId pps t
   let arg = id_t (getPosition t)
   let ty = cTCon tyId `fn` t
   expr <- genFrom pps t (CVar arg)
   let cls = CClause [CPVar arg] [] expr
   return (CValueSign (CDef (from_Id tyId) (CQType [] ty) [cls]))
mkFrom_ x = internalError "GenWrap::mkFrom_ "

from_Id :: Id -> Id
from_Id i = addInternalProp (mkIdPre fsFrom i)

genFrom :: [PProp] -> CType -> CExpr -> GWMonad CExpr
genFrom pps ty var =
 do
   --traceM ("genFrom type: " ++ (pfpAll ty))
   cint <- chkInterface ty
   case cint of
     Nothing -> internalError ("genFrom: " ++ pfpReadable ty)
     Just (ti, _, fts) -> do
       -- the top-level interface might have pragmas on it
       -- (do the work that "extendPrefixes" would have done, of adding
       -- the pragrams on the interface to the prefix so that it propagates
       -- to the fields)
       ifcPrags <- getInterfacePrags ti
       let prefixes = noPrefixes { ifcp_pragmas = ifcPrags }
       fieldBlobs <- mapM (meth prefixes ti) fts
       return $ blobsToIfc ti fts fieldBlobs
 where
   blobsToIfc ti fts fieldBlobs =
       let meths = [ CLValue (setInternal f) [CClause [] [] e] gs
                         | (f, e, gs) <- fieldBlobs ]
       in  Cinterface (getPosition fts) (Just ti) meths

   -- This returns a 3-tuple of a field Id (method or subifc),
   -- its defining expression, and its implicit condition (only for methods).
   -- Note: The Id is qualified, because it could be something not
   -- imported by the user (and this not available unqualified).
   meth :: IfcPrefixes -> Id -> FInf ->
           GWMonad (Id, CExpr, [CQual])
   meth prefixes ifcId (FInf f as r aIds) =
    do
      ciPrags <- getInterfaceFieldPrags ifcId f {- f should be qualifed -}
      --traceM ("ciPrags = " ++ ppReadable (ifcId, f, ciPrags))
      mi <- chkInterface r
      case (mi, as) of
        (Just (ti, _, fts), []) -> do
          newprefixes <- extendPrefixes prefixes ciPrags r f
          fieldBlobs <- mapM (meth newprefixes ti) fts
          let expr = blobsToIfc ti fts fieldBlobs
          return (f, expr, [])
        _ -> do
          isVec <- isVectorInterfaces r
          case (isVec, as) of
            (Just (n, tVec, isListN), []) -> do
               --traceM ("fromVec:" ++ (show tVec))
               let nums = [0..(n-1)] :: [Integer]
               let recurse num =
                       do newprefixes <- extendPrefixes prefixes ciPrags r f
                          meth newprefixes idVector (FInf (mkNumId num) [] tVec [])
               fieldBlobs <- mapM recurse nums
               let (es, gs) = unzip [(e, g) | (_, e, g) <- fieldBlobs]
               let vec = cToVector isListN es
               return (f, vec, concat gs)
            _ -> do
              isPA <- isPrimAction r
              isClock <- isClockType r
              isReset <- isResetType r
              isInout <- isInoutType r
              let isIot = isInout /= Nothing
              isAV <- isActionValue r
              let binf = binId prefixes f
              let wbinf = mkRdyId binf
              let sel = CSelect var
              let hasNoRdy = isAlwaysRdy pps wbinf ||
                             isAlwaysReadyIfc (ifcp_pragmas prefixes ++ ciPrags)
              let meth_guard = CApply eUnpack [sel wbinf]
              let qs = if (hasNoRdy || isClock || isReset || isIot)
                       then [] else [CQFilter meth_guard]
              let e = CApply (CVar id_fromWrapMethod) [sel binf]
              return (f, e, qs)


-- --------------------
-- genWrapE toplevel: mkInstances

-- The Generic representation of a wrapper type is the type being wrapped -
-- here we derive a Generic instance which uses the
-- "fromIfc_" function and calls the class method for the original interface.

mkInstances :: IfcTRec -> GWMonad [CDefn]
mkInstances trec = do
  genericInstance <- mkGeneric trec
  return [genericInstance]

mkGeneric :: IfcTRec -> GWMonad CDefn
mkGeneric (IfcTRec { rec_id = flat_id, rec_type = orig_ty, rec_rootid = orig_id }) = do
  ctxs <- mkCtxs orig_ty
  let pos = getPosition orig_id
      flat_ty = cTCon flat_id
      cqt = CQType ctxs $ cTApplys (cTCon idGeneric)
            [flat_ty, cTApplys (cTCon idMeta)
              [cTApplys (cTCon idMetaData)
               [cTStr (getIdBase orig_id) pos,
                cTStr (getIdQual orig_id) pos,
                tMkTuple pos [],
                cTNum 1 pos],
               TAp (cTCon idConc) orig_ty]]
      defn = Cinstance cqt
        [CLValue (unQualId idFrom)
          [CClause [CPVar id_x] [] $
            CCon idMeta [CCon idConc [cVApply (from_Id flat_id) [CVar id_x]]]] [],
         CLValue (unQualId idTo)
          [CClause [CPCon idMeta [CPCon idConc [CPVar id_x]]] [] $
            cVApply (to_Id flat_id) [CVar id_x]] []]
  return defn

-- XXX this duplicates work done elsewhere; just do one traversal and
-- XXX reuse it in genIfcField / mkTo / mkFrom / mkFromBind
mkCtxs :: CType -> GWMonad [CPred]
mkCtxs ty =
 do
   cint <- chkInterface ty
   case cint of
     Nothing -> internalError ("genFrom: " ++ pfpReadable ty)
     Just (_, _, fts) -> do
       css <- mapM meth fts
       let bits_types = unions css
           ctxs = [ CPred (CTypeclass idBits) [t, cTVarNum v]
                        | (t, v) <- zip bits_types tmpTyVarIds ]
       return ctxs
 where
   meth :: FInf -> GWMonad [CType]
   meth (FInf _ as r _) =
    do
      mi <- chkInterface r
      case (mi, as) of
        (Just (_, _, fts), []) -> do
          ctxss <- mapM meth fts
          return (unions ctxss)
        _ -> do
          isVec <- isVectorInterfaces r
          case (isVec, as) of
            (Just (n, tVec, isListN), []) ->
               meth (FInf (mkNumId 0) [] tVec [])
            _ -> do
              isPA <- isPrimAction r
              isClock <- isClockType r
              isReset <- isResetType r
              isInout <- isInoutType r
              isAV <- isActionValue r
              res_ctxs <-
                  case isInout of
                    Just iot -> return [iot]
                    _ -> if (isPA || isClock || isReset)
                          then return []
                          else
                           if isAV
                              then do
                                retType <- getAVType "genFrom" r
                                return [retType]
                              else return [r]
              let ctxs = nub (res_ctxs ++ as)
              return (ctxs)


-- --------------------
-- genWrapE toplevel: mkNewModDef

-- For a module def named <modname>, we generate the actual synthesis
-- boundary called "<modname>_" which has bitified arguments and wraps
-- around the actual module definition (lifted with liftM), unpacking
-- the values before applying the module def to them.

mkNewModDef :: M.Map Id GeneratedIfc -> ModDefInfo -> GWMonad CDefn
mkNewModDef genIfcMap (def@(CDef i (CQType _ t) dcls), cqt, vtis, vps) =
 do
   -- XXX This could have been stored in the moduledef info
   -- XXX (note that the first half is the "ts" in "vtis")
   let tr = case getArrows t of
              (_, TAp _ r) -> r
              _ -> internalError "GenWrap.mkNewModDef: tr"
   tyId <- flatTypeId vps tr    -- id of the Ifc_
   let ty = tmod (cTCon tyId)   -- type of new module

   -- sanity check the port names (clashes, bad identifiers, etc)
   let genifc = case (M.lookup tyId genIfcMap) of
                  Just res -> res
                  Nothing -> internalError ("mkNewModDef: can't find ifc: " ++
                                            ppReadable tyId)
       cfields = case genifc_cdefn genifc of
                   (Cstruct _ _ _ _ cs _) -> cs
                   _ -> internalError "GenWrap.mkNewModDef: cfields"
   -- XXX reverse the fields just to match the behvaior of the previous
   -- XXX compiler, which accumulated with fold rather than map
   ftps <- mapM collectIfcInfo (reverse cfields)
   -- get back the arg port to type mapping, for recording
   flgs <- getFlags
   --  arg_pts <- convEM $ checkModulePortNames flgs (getPosition i) vps vtis ftps
   let arg_pts = []

   let arg_infos = thd $ unzip3 vtis
       (vs, ts) = unzip $ concatMap extractVTPairs arg_infos

   -- based on the types of the arguments (and given their names)
   -- generate the expressions that convert from the bitified/blasted ports
   -- to the original arguments (of the original type) of the inner module
   exprs <- mapM convVar arg_infos

   -- make the new def
   let -- the call to the module body (as written by the user) with its
       -- un-bitified and vectorized arguments
       mexp = cApply 10 (CVar i) exprs
       -- statements to record the port-types of module arguments
       -- (for the current module)
       arg_sptStmts = map (uncurry saveTopModPortTypeStmt) arg_pts
       -- a do-block around the module body, so that we can include the
       -- save-port-type statements
       lexp = if not (null arg_sptStmts)
              then Cdo False (arg_sptStmts ++ [CSExpr Nothing mexp])
              else mexp
       -- liftM of the do-block
       to  = cVApply idLiftM [CVar (to_Id tyId), lexp]
       -- let-define the user's module around the expr we just created
       lte = Cletrec [CLValueSign def []] to
       -- the clause for the new def we're creating
       cls = CClause (map CPVar vs) [] lte

   -- produce the context and new base-type for the new def
   let tvs = map cTVarNum (take (length ts) tmpTyVarIds)
   -- reverse because we want to tack on the innermost type first
   -- and we are folding from the left
   (ctx, ty') <- foldM mkCtx ([], ty) (reverse (zip ts tvs))

   --traceM (" mkNewModDef: " ++ ppReadable def )
   --traceM (" mkNewModDef: dcls: " ++ ppReadable dcls)
   --traceM (" mkNewModDef: exprs: " ++ ppReadable exprs)
   --traceM ( "mkNewModDef: cls:" ++  ppReadable cls )
   let result =  (CValueSign (CDef (modIdRename vps i) (CQType ctx ty') [cls]))
   --traceM( "mkNewModDef tyId: " ++ ppReadable tyId )
   --traceM( "mkNewModDef vs: " ++ ppReadable vs )
   --traceM( "mkNewModDef res: " ++ ppReadable result )
   --traceM( "mkNewModDef def" ++ ppReadable def )
   return result
 where

   collectIfcInfo :: CField -> GWMonad  (Id, CType, [IfcPragma])
   collectIfcInfo (CField {cf_name = fid, cf_pragmas = ps,
                           cf_type = qtype@(CQType xpred ftype) }) = do
     -- XXX is this needed?
     ftype' <- expandSynSym ftype
     return (fid, ftype, fromMaybe [] ps)

   convVar :: ArgInfo -> GWMonad CExpr
   convVar (Simple v lt) =
     do
       cint <- chkInterface lt
       case cint of
         Just (ti, _, fts) -> -- interface arguments are not supported
                              bad (getPosition v,
                                   EInterfaceArg (pfpString i))
         Nothing ->
          do
            isInout <- isInoutType lt
            case isInout of
             Just _ -> return (CApply ePrimInoutUncast0 [CVar v])
             _ ->
              do
               isClock <- isClockType lt
               isReset <- isResetType lt
               isParam <- isParamType lt
               if (isClock || isReset || isParam)
                 then return (CVar v)
                 else return (CApply eUnpack [CVar v])
   convVar (Vector isListN _ _ sub_ports) = do
       -- get the expression for each port
       -- (which may split the ports further)
       elem_es <- mapM convVar sub_ports
       return $ cToVector isListN elem_es

   mkCtx :: ([CPred], Type) -> (Type, Type) -> GWMonad ([CPred], Type)
   mkCtx (ctx, rt) (lt, v) =
    do
      -- XXX interface argument remnant
      isgIfc <- isGoodInterface lt
      if isgIfc
        then do
          ft <- flatTypeId [] lt
          return (ctx, cTCon ft `fn` rt)
        else do
          isInout <- isInoutType lt
          case isInout of
            Just tt -> return ((CPred (CTypeclass idBits) [tt, v]):ctx,
                               TAp tInout_ v `fn` rt)
            _ -> do
                  isClock <- isClockType lt
                  isReset <- isResetType lt
                  isParam <- isParamType lt
                  if (isClock || isReset || isParam)
                     then return (ctx, lt `fn` rt)
                     else return ((CPred (CTypeclass idBits) [lt, v]):ctx, TAp tBit v `fn` rt)

mkNewModDef _ (def,_,_,_) =
    internalError ("GenWrap::mkNewModDef unexpected definition " ++ show def )


-- ==============================
-- The wrapper continuation

-- This is the part of "genWrapInfo" which makes the DefFun,
-- a continuation function which does the final wrapper computation.

-- type DefFun = VWireInfo -> VSchedInfo -> VPathInfo -> [VPort] -> SymTab -> [VFieldInfo] -> [Id] -> [Id] -> IO CDefn
-- XXX: alwaysEnabled is dropped and broken (not propagated to {inhigh})
mkDef :: [PProp] -> [PProp] -> CDef -> CQType -> GWMonad DefFun
mkDef iprags pps (CDef i (CQType _ qt) _) cqt = do
 st0 <- get
 return (\fmod wire_info sch pathinfo ips symt fields true_ifc_ids -> do
  let
      (ts, tr) = case getArrows qt of
                   (ats, TAp _ r) -> (ats, r)
                   _ -> internalError "GenWrap.mkDef: ts, tr"
      st1 = st0 { symtable = symt }
  -- do not use ifc prags here
  (st2, ti_) <- runGWMonadGetNoFail (flatTypeId pps tr) st1
  let vs =  take (length ts) tmpVarIds
  (st3, Just (_, _, finfs)) <- runGWMonadGetNoFail (chkInterface tr) st2
  let
      -- return an expression for creating the arg (from the wrapper's args)
      -- and the type of the internal module's arg (for port-type saving)
      genArg :: CExpr -> Type -> GWMonad [(CExpr, CType)]
      genArg vexpr t =
       do
         --traceM( "In genArg: " ++ ppReadable v ++ " " ++ ppReadable t ) ;
         cint <- chkInterface t
         case cint of
           Just x -> -- interface arguments are not supported and should
                     -- already have generated an error
                     internalError ("mkDef: ifc arg: " ++ ppReadable (t,x))
           Nothing -> do
             isInout <- isInoutType t
             case isInout of
              Just _ -> return [(CApply ePrimInoutCast0 [vexpr], t)]
              _ ->
               do
                 isClock <- isClockType t
                 isReset <- isResetType t
                 isParam <- isParamType t
                 if (isClock || isReset || isParam)
                   then return [(vexpr,t)]
                   else do isVector <- isVectorType t
                           case isVector of
                             Just (n,tVec,_) -> genVecArg vexpr n tVec
                             _ -> return [(CApply ePack [vexpr], t)]
      genVecArg :: CExpr -> Integer -> Type -> GWMonad [(CExpr, CType)]
      genVecArg vexpr sz tVec = do
         -- make the expression for each port
         let nums = [0..(sz-1)]
             primselect = idPrimSelectFn noPosition
             lit k = CLit $ num_to_cliteral_at noPosition k
             selector n = cVApply primselect [posLiteral noPosition,
                                              vexpr, lit n]
             elem_sels = map selector nums
         elem_exprs <- mapM (`genArg` tVec) elem_sels
         return (concat elem_exprs)

  (st4, argss) <- runGWMonadGetNoFail (zipWithM genArg (map CVar vs) ts) st3
  let (arg_exprs, arg_ts) = unzip $ concat argss
      -- make the arg port-types, for saving in the module
      arg_pts = mkArgPortTypes wire_info arg_ts
  let
      -- don't use the "fixed up" veriFields below because we don't need
      -- port property information (makes the flow a little simpler, I think)
      vfield_map = M.fromList [(vf_name vf, vf) | vf <- fields]

      fields' = filter (not . (isRdyToRemoveField (iprags ++ pps))) fields
      veriFields = (map (fixupVeriField (iprags ++ pps) ips) fields')
      vexp = xWrapperModuleVerilog
             fmod
             pps
             (CLit(CLiteral noPosition(LString( getIdBaseString i) )))
             wire_info
             arg_exprs
             veriFields
             sch
             pathinfo
      vlift = (cVApply idLiftModule [vexp])
  body <- runGWMonadNoFail
              (genFromBody arg_pts vfield_map vlift true_ifc_ids ti_ finfs)
              st4
  let cls = CClause (map CPVar vs) [] body
  return $ CValueSign (CDef i cqt [cls]))

mkDef _ _ def _ = internalError ("GenWrap::mkDef unexpected " ++ show def )


mkArgPortTypes :: VWireInfo -> [CType] -> [(VPort, CType)]
mkArgPortTypes wire_info arg_ts =
    let
        -- xWrapperModuleVerilog will check that the lists are the same length
        arg_its = zip (wArgs wire_info) arg_ts
        mkPortType (Port vp _ _, t) = [(vp,t)]
        mkPortType (InoutArg vn _ _, t) = [((vn,[]),t)]
        -- XXX fill in info for the rest?
        mkPortType (Param {}, _) = []
        mkPortType (ClockArg {}, _) = [] -- would need the osc and gate
        mkPortType (ResetArg {}, _) = []
    in
        concatMap mkPortType arg_its


-- used in wrapper generate to wrap the module given by mk
-- to the result.
genFromBody :: [(VPort, CType)] -> M.Map Id VFieldInfo ->
               CExpr -> [Id] -> Id -> [FInf] -> GWMonad CExpr
genFromBody arg_pts vfield_map mk true_ifc_ids si fts =
 do
   -- traceM( "genFromBody: " ++ ppReadable fts )
   let sty = cTCon si
   let pos = getIdPosition si
   let mkMethod = mkFromBind vfield_map true_ifc_ids (CVar (id_t pos))
   (meths, ifc_ptss) <- mapAndUnzipM mkMethod fts
   let -- interface save-port-type statements
       ifc_sptStmts =
           map (uncurry (savePortTypeStmt (CVar id_x))) (concat ifc_ptss)
       -- argument save-port-type statements
       arg_sptStmts =
           map (uncurry (savePortTypeStmt (CVar id_x))) arg_pts
       sptStmts = arg_sptStmts ++ ifc_sptStmts
   let tmpl = Cmodule pos $
                 [CMStmt $ CSBindT (CPVar (id_t pos)) Nothing [] (CQType [] sty) mk] ++
                 ((saveNameStmt (id_t pos) id_x):sptStmts) ++
                 [CMinterface (Cinterface pos Nothing meths)]
   -- traceM( "genFromBody return: " ++ (show mk))
   return tmpl


-- Creates a method for the module body
-- also returns the raw port-type information for correlation
-- XXX some of this can be replaced with a call to "mkFrom_"
mkFromBind :: M.Map Id VFieldInfo -> [Id] -> CExpr -> FInf -> GWMonad (CDefl, [(VPort, CType)])
mkFromBind vfield_map true_ifc_ids var ft =
 do
   ms <- meth noPrefixes ft
   return (mkv ms, fth4 ms)
 where
   mkv (f, e, g, _) = CLValue (setInternal f) [CClause vps [] e'] g
     where
       (vps, e') = unLams e
   -- This returns a triple of a field Id (method or subifc),
   -- its definition, and its implicit condition (only for methods).
   -- Note: The Id is qualified, because it could be something not
   -- imported by the user (and this not available unqualified).
   meth :: IfcPrefixes -> FInf -> GWMonad (Id, CExpr, [CQual], [(VPort, CType)])
   meth prefixes (FInf f as r aIds) =
    do
      mi <- chkInterface r
      case (mi, as) of
        (Just (ti, _, fts), []) -> do
          newprefixes <- extendPrefixes prefixes [] r f
          fieldBlobs <- mapM (meth newprefixes) fts
          return (f, cInterface ti (map fst3of4 fieldBlobs), [], concatMap fth4 fieldBlobs)
        _ -> do
          isVec <- isVectorInterfaces r
          case (isVec, as) of
            (Just (n, tVec, isListN), []) -> do
               --traceM ("fromVec:" ++ (show tVec))
               let nums = [0..(n-1)] :: [Integer]
               let recurse num = do newprefixes <- extendPrefixes prefixes [] r f
                                    meth newprefixes (FInf (mkNumId num) [] tVec [])
               fieldBlobs <- mapM recurse nums
               let (es, gs) = unzip [(e,g) | (_, e, g, _) <- fieldBlobs]
               let vec = cToVector isListN es
               return (f, vec, concat gs, concatMap fth4 fieldBlobs)
            _ -> do
              isPA <- isPrimAction r
              isClock <- isClockType r
              isReset <- isResetType r
              isInout <- isInoutType r
              let isIot = isInout/=Nothing
              isAV <- isActionValue r
              let binf = binId prefixes f
              let wbinf = mkRdyId binf
              let sel = CSelect var
              let meth_guard = CApply eUnpack [sel wbinf]
              let vs = take (length as) (aIds ++ tmpVarXIds)
              let qs = if (wbinf `elem` true_ifc_ids || isClock || isReset || isIot)
                       then [] else [CQFilter meth_guard]
              let ec = cApply 13 (sel binf) (map (\ v -> CApply ePack [CVar v]) vs)
              let e =
                   case isInout of
                    Just _ -> (CApply ePrimInoutUncast0 [ec])
                    _ -> if (isPA || isClock || isReset)
                          then ec
                          else
                           if isAV
                              then cApply 12 (CVar idFromActionValue_) [ec]
                              else CApply eUnpack [ec]
              pts <- case (M.lookup binf vfield_map) of
                       Just (Method { vf_inputs = inps,
                                      vf_output = mo }) -> do
                         output_type <- if isAV then
                                          getAVType "mkFromBind" r
                                         else return r
                         return ((maybeToList (fmap (\p -> (p, output_type)) mo)) ++
                                 zip inps as)
                       Just (Inout { vf_inout = vn }) -> do
                         let ty = r
                             vp = (vn, [])
                         return [(vp,ty)]
                       _ -> do --traceM ("no field info: " ++ ppReadable (f, binf, vfield_map))
                               return []
              return (f, cLams vs e, qs, pts)



-- add port properties to method ports in VModInfo
fixupVeriField :: [PProp] -> [(VName, [VeriPortProp])] -> VFieldInfo -> VFieldInfo
fixupVeriField _ _ f@(Clock { }) = f
fixupVeriField _ _ f@(Reset { }) = f
fixupVeriField _ _ f@(Inout { }) = f
fixupVeriField pps vportprops m@(Method { }) =
        m { vf_inputs = inputs',
            vf_output = output',
            vf_enable = enable'' }
  where inputs'  =  map fixup (vf_inputs m)
        output'  = fmap fixup (vf_output m)
        enable'  = fmap fixup (vf_enable m)
        fixup    = fixupPort vportprops
        alwaysEnabled = isAlwaysEn pps (vf_name m)
        enable'' = fmap (addInHigh alwaysEnabled) enable'

-- tack on extra port properties at the port level
fixupPort :: [(VName, [VeriPortProp])] -> VPort -> VPort
fixupPort vportprops vport@(vname, base_props) =
  case (lookup vname vportprops) of
    Nothing -> vport
    Just props -> (vname, base_props ++ props)

-- add inhigh prop to alwaysEnabled port
addInHigh :: Bool -> VPort -> VPort
addInHigh False p = p
addInHigh True (n, props)  = (n, VPinhigh:props)

cInterface :: Id -> [(Id, CExpr, [CQual])] -> CExpr
cInterface ti fegs =
        Cinterface (getPosition fegs) (Just ti) [CLValue (setInternal f) [CClause [] [] e] g | (f, e, g) <- fegs ]


-- ====================
-- Interface checking and associated type analysis utilities

-- Checks if a given type is an interface and, if so, it returns:
--  * interface id
--  * kind
--  * _qualified_ field info
-- (The qualified info is needed when we generate struct selectors
--  under the covers, because these may not be available to the user
--  but are available to genwrap by their qualified name.)
-- XXX this is called too many times to gather the same information.
chkInterface :: Type -> GWMonad (Maybe (Id, Kind, [FInf]))
chkInterface t = do
  --traceM("chkInterface: before: " ++ ppReadable(t))
  symt <- getSymTab
  t' <- expandSynSym t
  --traceM("chkInterface: after: " ++ ppReadable(t'))
  case (leftCon t') of
   Nothing -> return Nothing
   Just i -> do
    let ts = tyConArgs t'
    case findType symt i of
     Just (TypeInfo (Just ti) k vs (TIstruct ss fs)) | isIfc ss -> do
       anyPoly <- isAnyPolyFieldType ti ts fs
       if anyPoly
         then return Nothing
         else do
           finfs <- mapM (getFInf ti ts) fs
           return (Just (ti, k, finfs))
     _ -> return Nothing
 where
   getFInf ti ts f =
    do
      ft <- getFieldType ti ts f
      --traceM("getFInf: before: " ++ ppReadable(ft))
      ft_ext <- expandSynSym ft
      --traceM("getFInf: after: " ++ show(ft_ext))
      let (as, r) = case getArrows ft_ext of
                      (_:ats, rt) -> (ats, rt)
                      _ -> internalError "GenWrap.chkInterface: as, r"
      -- get any user-declared names for the arguments
      symt <- getSymTab
      let aIds = getMethodArgNames symt ti f
      return (FInf f as r aIds)

getFieldType :: Id -> [Type] -> Id -> GWMonad CType
getFieldType ifcType ts fieldId =
 do
   symt <- getSymTab
   case findField symt fieldId of
     Just xs -> do
       let finfos = [sc | (FieldInfo { fi_id = ti',
                                       fi_arity = n,
                                       fi_assump = (_ :>: sc) }) <- xs,
                          ifcType == ti']
       case finfos of
         [Forall ks t] -> do
           case inst ts t of
             [] :=> lt -> return lt
             p -> internalError ("getFieldType: 1 " ++ pfpReadable p)
         ys -> internalError ("getFieldType: 2 " ++ ppString (xs, (ifcType, fieldId), ys))
     Nothing -> internalError ("getFieldType: 3 " ++ ppString (ifcType, fieldId))

isAnyPolyFieldType :: Id -> [Type] -> [Id] -> GWMonad Bool
isAnyPolyFieldType ti ts [] = return False
isAnyPolyFieldType ti ts (c:cs) =
 do
   res <- isPolyFieldType ti ts c
   anyPoly <- isAnyPolyFieldType ti ts cs
   return (res || anyPoly)

isPolyFieldType :: Id -> [Type] -> Id -> GWMonad Bool
isPolyFieldType ti ts c =
 do
   symt <- getSymTab
   case findField symt c of
     Just xs -> do
       let finfos = [ sc | (FieldInfo { fi_id = ti',
                                        fi_arity = n,
                                        fi_assump = (_ :>: sc) }) <- xs,
                           ti == ti']
       case finfos of
         [Forall ks t] -> return (length ks /= length ts)
         ys -> internalError ("isPolyFieldType: 2 " ++ ppString (xs, (ti, c), ys))
     Nothing -> internalError ("isPolyFieldType: 3 " ++ ppString (ti, c))

isVectorInterfaces :: Type -> GWMonad (Maybe (Integer, Type, Bool))
isVectorInterfaces t =
 do
   t' <- isVectorType t
   case (t') of
     Just (n,tVec, isListN) -> do
       res <- chkInterfaceVectorElementType tVec
       if (res) then
         return (Just (n, tVec, isListN))
        else return Nothing
     _ -> return Nothing

-- is the supplied type a valid component of a vector of interfaces?
-- this includes Clocks, Resets, interfaces and vectors of such types
chkInterfaceVectorElementType :: Type -> GWMonad (Bool)
chkInterfaceVectorElementType t =
 do
   t' <- isVectorType t
   case (t') of
     Just (_,tVec,_) -> chkInterfaceVectorElementType tVec
     Nothing -> do
         isClock <- isClockType t
         isReset <- isResetType t
         if (isClock || isReset) then return True
          else do
            inout <- isInoutType t
            if (isJust inout) then return True
             else do ifc <- chkInterface t
                     return (isJust ifc)

-- --------------------

-- XXX use of "qualEq" is wrong, but "genFuncWrap" generates unqualified names

-- XXX get rid of "isPrimAction" because there should not be raw PrimActions
isPrimAction :: Type -> GWMonad Bool
isPrimAction t =
 do
   et <- expandSynSym t
   case et of
     TCon (TyCon i _ _) -> return (qualEq i idPrimAction)
     _ -> return False

isActionValue :: Type -> GWMonad Bool
isActionValue t =
 do
   et <- expandSynSym t
   case et of
        (TAp (TCon (TyCon i _ _)) _) -> return (qualEq i idActionValue)
        _ -> return False

getAVType :: String -> Type -> GWMonad (Type)
getAVType tag xt =
 do
   et <- expandSynSym xt
   case et of
     TAp (TCon (TyCon i _ _)) t | qualEq i idActionValue -> return t
     _ -> internalError (tag ++ " getAVType " ++ ppReadable xt)


-- is the type a valid Verilog parameter (but not a wire or bitifiable port)?
isParamType :: Type -> GWMonad Bool
isParamType t =
  do
    t' <- expandSynSym t
    return (t' == tReal || t' == tString)

isClockType :: Type -> GWMonad Bool
isClockType t =
 do
   t' <- expandSynSym t
   return   (t' == tClock)

isResetType :: Type -> GWMonad Bool
isResetType t =
 do
   t' <- expandSynSym t
   return   (t' == tReset)

isInoutType :: Type -> GWMonad (Maybe Type)
isInoutType t =
 do
   t' <- expandSynSym t
   case  t' of
            (TAp tt ta) | (tt == tInout) -> return (Just ta)
            _          -> return Nothing

isVectorType :: Type -> GWMonad (Maybe (Integer, Type, Bool))
isVectorType t =
 do
   t' <- expandSynSym t
   case (leftCon t', tyConArgs t') of
     (Just con, [TCon (TyNum n _), tVec])
         | ((qualEq con idListN) || (qualEq con idVector))
       -> return $ Just (n,tVec,qualEq con idListN)
     _ -> return $ Nothing

-- --------------------

expandSynSym :: Type -> GWMonad Type
expandSynSym xt =
 do
   symt <- getSymTab
   return (expandSyn (updTypes symt xt))
 where
   updTypes r o@(TCon (TyCon i _ TIabstract)) =
     case findType r i of
       Just (TypeInfo (Just i') k _ ti) -> TCon (TyCon i' (Just k) ti)
       Just (TypeInfo Nothing _ _ _) ->
         internalError ("genWrap: expandSynSym: unexpected numeric type:" ++
                        ppReadable i)
       Nothing -> o
   updTypes r (TAp f a) = TAp (updTypes r f) (updTypes r a)
   updTypes r t = t

-- --------------------

-- Create a qualified ID, based on the specific (interface) type generated
-- the first part of the name is based on the type of the interface, while the second is
-- based on the specific pragmas, AR/AE from the PProps
flatTypeIdQual :: [PProp] -> CType -> GWMonad Id
flatTypeIdQual pps sty =
 do
   esty <- expandSynSym sty
   let qual = case esty of
          TCon (TyCon i _ _) -> fst (getIdFStrings i);
          _                  -> fsEmpty
   let flat_fs = concatFString (map (getIdFString . unQualId) (flattenType esty))
   let flat_id = mkQId noPosition qual flat_fs
   return (ifcIdRename pps flat_id)
   --
 where
   flattenType :: CType -> [Id]
   flattenType (TVar (TyVar i _ _)) = [i] -- xxx aren't any at top level
   flattenType (TCon (TyCon i _ _)) = [i]
   flattenType (TCon (TyNum i _)) = [mkNumId i]
   flattenType (TAp t1 t2) = flattenType t1 ++ flattenType t2
   flattenType t = internalError ("GenWrap::flattenType: " ++ pfpReadable t)

flatTypeId :: [PProp] -> CType -> GWMonad Id
flatTypeId pps ty =
 do
   res <- flatTypeIdQual pps ty
   return (unQualId res)

-- extract the name ID  from the type
rawTypeId :: CType -> GWMonad Id
rawTypeId sty =
 do
   symt <- getSymTab
   esty <- expandSynSym sty
   let raw = extractId esty
   -- keep the qualified name
   return raw
 where
   extractId ltype = case ltype of
         TCon (TyCon i _ _) -> i
         TAp r _            -> extractId r
         _                  -> internalError ("GenWrap :: rawTypeId: " ++ show ltype )


-- ====================
-- Prefix utilities (for flattening interfaces)

-- structure to hold names, prefix strings, and pragmas passed from parent interfaces
-- down to specific fields.
data  IfcPrefixes = IfcPrefixes
    {
     ifcp_pathIdString   :: [FString], -- list of paths to root.  all methods will be renamed via this
     ifcp_renamePrefixes :: String,
     ifcp_pragmas        :: [IfcPragma]
    }

instance PPrint IfcPrefixes where
    pPrint d p ip =
        text "IfcPrefix:" <+> pPrint d p (ifcp_pathIdString ip) <+>
        doubleQuotes (text (ifcp_renamePrefixes ip)) <+> pPrint d p (ifcp_pragmas ip)

noPrefixes :: IfcPrefixes
noPrefixes = IfcPrefixes {
                                         ifcp_pathIdString   = [],
                                         ifcp_renamePrefixes = "",
                                         ifcp_pragmas        = [] }

-- builds a qualified path for the interface field name
-- FString is the hierarchy path
binId :: IfcPrefixes -> Id -> Id
-- XXX horrible hack when there isn't selection required at the end
binId ifcp i | i == idEmpty =  mkId noPosition (concatFString (init (ifcp_pathIdString ifcp)))
binId ifcp i = (mkIdPre (concatFString (ifcp_pathIdString ifcp)) (unQualId i))

-- Extend the prefixes
-- Take the current set of prefix information, add to that information
-- from the the pragma of the current field Id, and add it to the current set of
-- information
-- Generate a new set of prefixes since the field Id is an interface and we have to traverse down it.
extendPrefixes :: IfcPrefixes -> [IfcPragma] -> CType -> Id -> GWMonad IfcPrefixes
-- XXX idEmpty is a horrible way to know we're not terminating on an interface..
extendPrefixes ifcp _ _ fid | fid == idEmpty = return ifcp
extendPrefixes ifcp iprags ifct fid =
    do  localiprags <- getInterfacePrags (getResultIdFromType ifct)
        return IfcPrefixes {
                            ifcp_pathIdString = newPP,
                            ifcp_renamePrefixes = renames',
                            ifcp_pragmas = aear ++ localiprags
                           }
    where pathPrefix = ifcp_pathIdString ifcp
          renames = ifcp_renamePrefixes ifcp
          -- the new prefix is the just the path extended with the current path.
          newPP = pathPrefix ++ [getIdBase fid, fsUnderscore]
          -- The new prefix string come from the user speced prefix of the interface name
          mpre = fromMaybe (getIdBaseString fid) (lookupPrefixIfcPragma iprags )
          renames' = joinStrings_  renames mpre
          -- consider only the AE AR pragma here, the prefix is accounted for above,
          -- and it is not needed for levels below.
          aear = getARAEPragmas (iprags ++ (ifcp_pragmas ifcp) )


getResultIdFromType :: CType -> Id
getResultIdFromType ftype = fromMaybe err (leftCon (getRes ftype))
    where
    err = internalError( "getResultIdFromType: " ++ show ftype)


-- ====================
-- Pragma utilities

-- We want to fill out the pragma list.   Adding prefixes to all the names, NO NO NO this is called at the top
-- we want to extract all th prefixes, here and generate a list of Ifc Pragmas to add
-- the only thing itneresting is AR, AE.
getInterfaceFieldPrags ::  Id -> Id -> GWMonad [IfcPragma]
getInterfaceFieldPrags  ifcId fieldId  =
    do
       symt <- getSymTab
       let fprags :: [IfcPragma]
           fprags = maybe [] fi_pragmas (findFieldInfo symt ifcId fieldId)
       return fprags

getInterfacePrags :: Id -> GWMonad [IfcPragma]
getInterfacePrags ifcId =
    do symt <- getSymTab
       let r = case (findType symt ifcId) of
                   Nothing -> []
                   Just (TypeInfo mi knd vs tis) ->
                       case tis of
                           TIstruct (SInterface prags) _ -> prags
                           _                             -> []
       return r


-- generate a full set of pragmas for the new method which is being created.
-- these pragmas are then loaded in the symbol table, and picked out during eval for name creation.
genNewMethodIfcPragmas :: IfcPrefixes -> [IfcPragma] -> Id -> Id -> ([PProp], [IfcPragma])
genNewMethodIfcPragmas ifcp pragmas fieldId newFieldId  =
    (par ++ pae ,( prefix:resName:rdyName:enName:(args ++ ar ++ ae)))
    where methodStr = getIdString fieldId
          currentPre  = ifcp_renamePrefixes ifcp -- the current rename prefix
          --
          localPrefix1 = fromMaybe (getIdString fieldId) (lookupPrefixIfcPragma pragmas)
          localPrefix = joinStrings_  currentPre localPrefix1
          --
          prefix = (PIPrefixStr localPrefix)
          -- arg names are unchanged.
          args    = [a | a@(PIArgNames {} ) <- pragmas]
          -- find AR/AE signals  look for these in parents as well
          joinedPrags = pragmas ++ ifcp_pragmas ifcp
          ar = if (isAlwaysReadyIfc joinedPrags)   then [PIAlwaysRdy     ] else []
          ae = if (isAlwaysEnabledIfc joinedPrags) then [PIAlwaysEnabled ] else []
          -- The result names used the prefix plus the given of generated name
          mResName = lookupResultIfcPragma pragmas
          resultName =  case mResName of
                        Just str -> joinStrings_ currentPre str
                        Nothing  -> joinStrings_ currentPre methodStr
          --
          resName = (PIResultName resultName)
          -- The ready name
          mRdyStr = lookupRdySignalIfcPragma pragmas
          readyName =  case mRdyStr of
                       Just str -> joinStrings_ currentPre  str
                       Nothing  -> (getFString fs_rdy) ++ (joinStrings_ currentPre methodStr)
          rdyName = (PIRdySignalName  readyName)
          -- The Enable name
          mEnStr = lookupEnSignalIfcPragma pragmas
          enableName =  case mEnStr of
                        Just str -> joinStrings_ currentPre  str
                        Nothing  -> (getFString fsEnable) ++ (joinStrings_ currentPre methodStr)
          enName = (PIEnSignalName  enableName)
          -- Now the module properties
          -- we need to look the local as well as the parents pragmas
          par = if (isAlwaysReadyIfc   joinedPrags) then [PPalwaysReady   [[newFieldId]]] else []
          pae = if (isAlwaysEnabledIfc joinedPrags) then [PPalwaysEnabled [[newFieldId]]] else []


-- generate a full set of pragmas for the new clock field which is being created.
-- these pragmas are then loaded in the symbol table, and picked out during eval for name creation.
genNewClockIfcPragmas :: IfcPrefixes -> [IfcPragma] -> Id -> Id -> ([PProp], [IfcPragma])
genNewClockIfcPragmas ifcp pragmas fieldId newFieldId  =
    ([] , [prefix])
    where currentPre  = ifcp_renamePrefixes ifcp -- the current rename prefix
          --
          localPrefix1 = fromMaybe (getIdString fieldId) (lookupPrefixIfcPragma pragmas)
          localPrefix = joinStrings_  currentPre localPrefix1
          --
          prefix = (PIPrefixStr localPrefix)


-- generate a full set of pragmas for the new reset field which is being created.
-- these pragmas are then loaded in the symbol table, and picked out during eval for name creation.
genNewResetIfcPragmas :: IfcPrefixes -> [IfcPragma] -> Id -> Id -> ([PProp], [IfcPragma])
genNewResetIfcPragmas ifcp pragmas fieldId newFieldId  =
    ([] , [prefix])
    where currentPre  = ifcp_renamePrefixes ifcp -- the current rename prefix
          --
          localPrefix1 = fromMaybe (getIdString fieldId) (lookupPrefixIfcPragma pragmas)
          localPrefix = joinStrings_  currentPre localPrefix1
          --
          prefix = (PIPrefixStr localPrefix)


-- generate a full set of pragmas for the new inout field which is being created.
-- these pragmas are then loaded in the symbol table, and picked out during eval for name creation.
genNewInoutIfcPragmas :: IfcPrefixes -> [IfcPragma] -> Id -> Id -> ([PProp], [IfcPragma])
genNewInoutIfcPragmas ifcp pragmas fieldId newFieldId  =
    ([] , [prefix])
    where currentPre  = ifcp_renamePrefixes ifcp -- the current rename prefix
          --
          localPrefix1 = fromMaybe (getIdString fieldId) (lookupPrefixIfcPragma pragmas)
          localPrefix = joinStrings_  currentPre localPrefix1
          --
          prefix = (PIPrefixStr localPrefix)


-- Join string together with an underscore if either is not empty.
joinStrings_ :: String -> String -> String
joinStrings_  "" s2 = s2
joinStrings_  s1 "" = s1
joinStrings_  s1 s2 = s1 ++ "_" ++ s2

-- --------------------

-- Check that the names exist
-- XXX also check that always_enabled isn't applied to a value method?
chkUserPragmas :: [PProp] -> GeneratedIfc -> GWMonad ()
chkUserPragmas pps ifc = do
    -- find any names mentioned by the user
    let getMethIds (PPalwaysReady is) = is
        getMethIds (PPalwaysEnabled is) = is
        getMethIds (PPenabledWhenReady is) = is
        getMethIds _ = []
    let pp_ids = map flattenUSId $ -- turn Longname into Id
                 concatMap getMethIds pps
    when (null pp_ids) $ return ()

    -- find the fields of the flattened ifc
    let fields = case genifc_cdefn ifc of
                   (Cstruct _ _ _ _ cs _) -> cs
                   _ -> internalError "GenWrap.chkUserPragmas: fields"

    -- identify which fields are methods
    let dropQ (CQType _ t) = t
    let isMethType t = do
          let tt = dropQ t
          isClock <- isClockType tt
          isReset <- isResetType tt
          isInout <- isInoutType tt
          return (not isClock && not isReset && isInout==Nothing)
    meth_fields <- filterM (isMethType . cf_type) fields
    -- and get their flattened ids
    let meth_ids = map cf_name meth_fields

    let bad_pp_ids = filter (\i -> not (elem i meth_ids)) pp_ids
        mkErr i = (getPosition i, EAttributeIdNotAMethod (getIdString i))
    if (null bad_pp_ids)
        then return ()
        else bads $ map mkErr bad_pp_ids


-- ====================
-- Saving name/type information

-- liftModule $ primSavePortType (Valid v) s t
savePortTypeStmt :: CExpr -> (VName, b) -> CType -> CMStmt
savePortTypeStmt v (VName s, _) t =
  CMStmt $ CSExpr Nothing $
    cVApply idLiftModule $
      [cVApply idSavePortType
        [mkMaybe (Just v), stringLiteralAt noPosition s, typeLiteral t]]

-- liftModule $ primSavePortType (Valid v) s (typeOf e)
savePortTypeOfStmt :: CExpr -> (VName, b) -> CExpr -> CMStmt
savePortTypeOfStmt v (VName s, _) e =
  CMStmt $ CSExpr Nothing $
    cVApply idLiftModule $
      [cVApply idSavePortType
        [mkMaybe (Just v), stringLiteralAt noPosition s, cVApply idTypeOf [e]]]

-- primSavePortType Invalid i t
saveTopModPortTypeStmt :: Id -> CType -> CStmt
saveTopModPortTypeStmt i t =
  let s = getIdBaseString i
  in  CSExpr Nothing $
        cVApply idSavePortType
          [mkMaybe Nothing, stringLiteralAt noPosition s, typeLiteral t]

saveNameStmt :: Id -> Id -> CMStmt
saveNameStmt svName resultVar = CMStmt (CSletseq [(CLValue resultVar [CClause [] [] nameExpr]) []])
  where nameExpr = cVApply idGetModuleName [cVApply idAsIfc [CVar svName]]


-- ====================
-- CSyntax utilities

extSel :: CExpr -> Id -> CExpr
extSel sel xid | xid == idEmpty = sel
extSel sel xid = CSelect sel xid

cLams :: [Id] -> CExpr -> CExpr
cLams is e = foldr (CLam . Right) e is

unLams :: CExpr -> ([CPat], CExpr)
unLams (CLam (Right i) e) = ((CPVar i):is, e') where (is, e') = unLams e
unLams (CLam (Left p) e) = ((CPAny p):is, e') where (is, e') = unLams e
unLams e = ([], e)

cToVector :: Bool -> [CExpr] -> CExpr
cToVector isListN es = cVApply f [vcons es]
  where vcons [] = CCon (idNil noPosition) []
        vcons (x:xs) = CCon (idCons noPosition) [x, vcons xs]
        f = if isListN then idToListN else idToVector

eUnpack :: CExpr
eUnpack = CVar idUnpack
ePack :: CExpr
ePack = CVar idPack
ePrimInoutCast0 :: CExpr
ePrimInoutCast0 = CVar idPrimInoutCast0
ePrimInoutUncast0 :: CExpr
ePrimInoutUncast0 = CVar idPrimInoutUncast0

-- converts type (ifc) to TAp Module -> ifc
tmod :: CType -> CType
tmod t = TAp (cTCon idModule) t

id_t :: Position -> Id
id_t pos = mkId pos fs_t


-- ====================
-- Ready method utilities

isRdyToRemoveField :: [PProp] -> VFieldInfo -> Bool
isRdyToRemoveField pps f = isAlwaysRdy pps (vf_name f)


hasReadyFN :: [VFieldInfo] -> VFieldInfo -> Bool
hasReadyFN vfs xvf = or (map (isReadyFor xvf) vfs)
 where
   isReadyFor vf@(Method {}) vf_rdy = (mkRdyId (vf_name vf)) == (vf_name vf_rdy)
   isReadyFor _ _ = False


-- ====================
-- XXX Interface argument remnants

getInterfaces :: [Type] -> GWMonad [Type]
getInterfaces ts =
 do
   filterM isGoodInterface ts

isGoodInterface :: Type -> GWMonad Bool
isGoodInterface t =
 do
   res <- chkInterface t
   case res of
     Just _ -> return True
     Nothing -> return False


-- ====================
