{-# LANGUAGE CPP #-}
module Main_tconcheck(main) where

-- tconcheck: verify the compiler's handwritten type-constructor constants
-- against the compiled Prelude.
--
-- BSC's front end enforces one type constructor per qualified name, so a
-- qualified Id determines its (kind, sort) payload.  Comparison code relies
-- on this invariant (TyCon/ITCon comparisons are by Id; see CType.hs and
-- IType.hs), and the compiler contains handwritten copies of tycon payloads
-- that could silently drift from the Prelude-derived truth:
--
--   * Type.handwrittenTCons        (src/comp/Type.hs)
--   * ISyntaxUtil.handwrittenITCons (src/comp/ISyntaxUtil.hs)
--   * StdPrel.preTypes and the tyConOf fields of StdPrel.preClasses,
--     which are added to the symbol table through independent paths
--     (MakeSymTab.addTypesUQ / addClassesUQ) with nothing else enforcing
--     agreement.
--
-- This tool obtains a symbol table containing the Prelude the production
-- way -- the same .bo reading (BinUtil.readImports) and symbol-table
-- construction (MakeSymTab.mkSymTab) that bsc itself uses -- and compares
-- every registered constant's kind and sort against it.  It is run during
-- the build, right after the Prelude libraries are compiled, so an edit to
-- the Prelude that changes a payload fails the build instead of silently
-- drifting.
--
-- Exit status 0 iff every entry is OK (or explicitly exempted/waived below).

import Control.Monad(forM)
import Data.List(isPrefixOf)
import qualified Data.Map as M
import System.Environment(getArgs, lookupEnv)
import System.Exit(exitWith, ExitCode(..))
import System.IO

import Error(initErrorHandle)
import Flags(Flags(..))
import FlagsDecode(defaultFlags)
import Id
import Util(fromJustOrErr)
import PPrint(ppString)
import CSyntax(CPackage(..), CImportedSignature(..), CSignature(..))
import CType(Type(..), TyCon(..), TISort, Kind, CTypeclass(..))
import Type(handwrittenTCons)
import IType(IType(..), IKind)
import ISyntaxUtil(handwrittenITCons)
import IConv(iConvK)
import StdPrel(preTypes, preClasses)
import Pred(Class(..))
import SymTab(SymTab, TypeInfo(..), findType)
import BinUtil(BinMap, readImports, replaceImportedSignatures)
import MakeSymTab(mkSymTab)

-- -------------------------
-- Exemptions and waivers

-- Constants for genuinely internal pseudo-tycons that are never entered in
-- any symbol table.  Missing-from-symtab is otherwise reported as DRIFT.
-- (Currently there are none: every registered constant names a type that
-- the Prelude declares or that StdPrel seeds into the symbol table.)
exemptMissing :: [(Id, String)]
exemptMissing = []

-- Entries confirmed to drift from the Prelude truth, pending direction on
-- the fix.  These are reported loudly (as DRIFT-WAIVED) but do not fail
-- the check, so that the build stays green while the fix is decided.
-- This list should shrink to empty over time; do NOT add new entries to
-- paper over a check failure.
--
-- All of the entries below are pre-existing: they have been masked for
-- years by the fact that TyCon Eq/Ord ignore the sort and ITCon
-- comparisons ignore both kind and sort (see CType.hs and IType.hs).
knownDrift :: [(String, String)]  -- (section ++ " " ++ name, reason)
knownDrift =
    [ ("Type Prelude.Int",
       "Prelude.bs declares 'data Int n = Int (Bit n)'; handwritten sort predates it (TIabstract)")
    , ("Type Prelude.UInt",
       "Prelude.bs declares 'data UInt n = UInt (Bit n)'; handwritten sort predates it (TIabstract)")
    , ("Type Prelude.PrimPair",
       "Prelude.bs declares PrimPair as an interface (TIstruct (SInterface []) ...); handwritten sort says SStruct")
    , ("Type Prelude.ActionValue",
       "Prelude.bs declares 'data ActionValue a = ActionValue ...'; handwritten sort is the old struct representation")
    , ("Type Prelude.ActionValue_",
       "ActionValue_ field names are avValue_/avAction_ in Prelude.bs; handwritten sort has the old __value/__action")
    , ("Type Prelude.File",
       "Prelude.bs declares 'data File = InvalidFile | MCD .. | FD ..'; handwritten sort predates it (TIabstract)")
    , ("ISyntaxUtil Prelude.Inout",
       "itInout has kind # -> * (apparently copied from itInout_); Inout's kind is * -> *")
    , ("ISyntaxUtil Prelude.PrimPair",
       "itPrimPair's kind is left-nested, (* -> *) -> *, because IKFun has no fixity declaration (defaults to infixl 9); also the SStruct-vs-SInterface sort, as in Type.hs")
    , ("ISyntaxUtil Prelude.BufferMode",
       "BlockBuffering carries a Maybe Integer argument, so BufferMode is not an enum; tiBufferMode says tiEnum")
    ]

-- -------------------------
-- Verdicts

data Verdict
    = VOk
    | VExempt String            -- reason
    | VWaived String [String]   -- reason, drift details
    | VDrift [String]           -- drift details

isDrift :: Verdict -> Bool
isDrift (VDrift _) = True
isDrift _ = False

isOk :: Verdict -> Bool
isOk VOk = True
isOk _ = False

-- Apply the knownDrift waiver list
applyWaiver :: String -> String -> Verdict -> Verdict
applyWaiver section name (VDrift details) =
    case lookup (section ++ " " ++ name) knownDrift of
      Just reason -> VWaived reason details
      Nothing -> VDrift details
applyWaiver _ _ v = v

-- -------------------------
-- Comparisons against the symbol table

-- compare a handwritten (Maybe Kind, TISort) against the symtab payload
checkCT :: SymTab -> Id -> Maybe Kind -> TISort -> Verdict
checkCT symt i mk s =
    case findType symt i of
      Nothing -> missingVerdict i
      Just (TypeInfo _ k _ s' _) ->
          mkVerdict $
              (if mk == Just k then []
               else ["kind: handwritten = " ++ maybe "(none)" ppString mk
                     ++ ", Prelude = " ++ ppString k])
           ++ (if s == s' then []
               else ["sort: handwritten = " ++ ppString s
                     ++ ", Prelude = " ++ ppString s'])

-- compare a handwritten (IKind, TISort) against the symtab payload,
-- bridging the kind with iConvK (the production Kind -> IKind conversion)
checkIT :: SymTab -> Id -> IKind -> TISort -> Verdict
checkIT symt i ik s =
    case findType symt i of
      Nothing -> missingVerdict i
      Just (TypeInfo _ k _ s' _) ->
          mkVerdict $
              (if iConvK k == ik then []
               else ["kind: handwritten = " ++ ppString ik
                     ++ ", Prelude = " ++ ppString (iConvK k)])
           ++ (if s == s' then []
               else ["sort: handwritten = " ++ ppString s
                     ++ ", Prelude = " ++ ppString s'])

missingVerdict :: Id -> Verdict
missingVerdict i =
    case lookup i exemptMissing of
      Just why -> VExempt why
      Nothing -> VDrift ["not present in the Prelude symbol table"]

mkVerdict :: [String] -> Verdict
mkVerdict [] = VOk
mkVerdict details = VDrift details

-- -------------------------
-- The four check sections

type Entry = (String, String, Verdict)  -- (section, name, verdict)

-- 1. Type.hs TCon constants vs symtab
checkTCons :: SymTab -> [Entry]
checkTCons symt = map chk handwrittenTCons
  where
    section = "Type"
    chk (TCon (TyCon i mk s)) =
        (section, getIdString i, checkCT symt i mk s)
    chk t =
        (section, ppString t, VDrift ["registered entry is not a TCon literal"])

-- 2. ISyntaxUtil.hs (and IType.hs) ITCon constants vs symtab
checkITCons :: SymTab -> [Entry]
checkITCons symt = map chk handwrittenITCons
  where
    section = "ISyntaxUtil"
    chk (ITCon i ik s) =
        (section, getIdString i, checkIT symt i ik s)
    chk t =
        (section, ppString t, VDrift ["registered entry is not an ITCon literal"])

-- 3. StdPrel.preTypes rows vs symtab (these seed the symtab, so this mainly
-- guards against a row being shadowed or dropped on an import path)
checkPreTypes :: SymTab -> [Entry]
checkPreTypes symt = map chk preTypes
  where
    section = "StdPrel.preTypes"
    chk (TypeInfo (Just i) k _ s _) =
        (section, getIdString i, checkCT symt i (Just k) s)
    chk ti =
        (section, ppString ti, VDrift ["preTypes row without a qualified Id"])

-- 4. StdPrel.preClasses: each class's tyConOf payload vs the symtab, and vs
-- its preTypes row (the internal twin pair: MakeSymTab adds preTypes and
-- preClasses through independent paths with nothing enforcing agreement)
checkClasses :: SymTab -> [Entry]
checkClasses symt = concatMap chk (preClasses symt)
  where
    preTypeMap = M.fromList [ (i, (k, s))
                              | TypeInfo (Just i) k _ s _ <- preTypes ]
    chk cls =
        let CTypeclass ci = name cls
        in  case tyConOf cls of
              TyCon i mk s ->
                  [ ("StdPrel.preClasses(symtab)", getIdString ci,
                     checkCT symt i mk s)
                  , ("StdPrel.preClasses(preTypes)", getIdString ci,
                     checkPair i mk s)
                  ]
              tc ->
                  [ ("StdPrel.preClasses", getIdString ci,
                     VDrift ["tyConOf is not a TyCon: " ++ ppString tc]) ]
    checkPair i mk s =
        case M.lookup i preTypeMap of
          Nothing -> VDrift ["class has no preTypes row"]
          Just (k, s') ->
              mkVerdict $
                  (if mk == Just k then []
                   else ["kind: tyConOf = " ++ maybe "(none)" ppString mk
                         ++ ", preTypes = " ++ ppString k])
               ++ (if s == s' then []
                   else ["sort: tyConOf = " ++ ppString s
                         ++ ", preTypes = " ++ ppString s'])

-- -------------------------

usage :: IO a
usage = do
    hPutStrLn stderr "Usage: tconcheck [libraries-dir]"
    hPutStrLn stderr "  (default: $BLUESPECDIR/Libraries)"
    exitWith (ExitFailure 2)

main :: IO ()
main = do
    hSetEncoding stdout utf8
    errh <- initErrorHandle
    as <- getArgs
    libdir <- case as of
                [] -> do mbsdir <- lookupEnv "BLUESPECDIR"
                         case mbsdir of
                           Just bsdir | not (null bsdir)
                               -> return (bsdir ++ "/Libraries")
                           _ -> do hPutStrLn stderr
                                     "tconcheck: BLUESPECDIR is not set"
                                   usage
                [dir] | not ("-" `isPrefixOf` dir) -> return dir
                _ -> usage
    -- Read the Prelude the production way: an empty in-memory package gets
    -- the implicit Prelude/PreludeBSV imports (BinUtil.addPrelude), whose
    -- .bo files are read with the production binary reader, and the symbol
    -- table is built by the same MakeSymTab.mkSymTab that bsc invokes.
    let flags = (defaultFlags "") { ifcPath = [libdir] }
        probe = CPackage (mk_homeless_id "TConCheckProbe")
                         (Right []) [] [] [] [] []
    (cpkg@(CPackage _ _ _ impsigs _ _ _), binmap, _)
        <- readImports errh flags (M.empty :: BinMap ()) M.empty probe
    -- Use the full (all-defs) signatures, not just the user-visible ones,
    -- exactly as bsc does when constructing the symbol table for module
    -- generation (see bsc.hs, DFsympostbinary): some checked constants
    -- (e.g. Pred__, SchedPragma) name types that the Prelude declares but
    -- does not export
    let findFn i = fromJustOrErr "tconcheck: binmap" $ M.lookup i binmap
        fullsigs = [ bo_sig
                     | CImpSign _ _ (CSignature si _ _ _) <- impsigs,
                       let (_, _, bo_sig, _, _) = findFn (getIdString si) ]
        cpkgFull = replaceImportedSignatures cpkg fullsigs
    symt <- mkSymTab errh cpkgFull

    putStrLn ("tconcheck: checking handwritten tycon constants against "
              ++ libdir)
    let entries = checkTCons symt
               ++ checkITCons symt
               ++ checkPreTypes symt
               ++ checkClasses symt
        entries' = [ (sec, nm, applyWaiver sec nm v)
                     | (sec, nm, v) <- entries ]
    results <- forM entries' $ \ (section, nm, verdict) -> do
        let tag = case verdict of
                    VOk -> "OK           "
                    VExempt _ -> "EXEMPT       "
                    VWaived _ _ -> "DRIFT-WAIVED "
                    VDrift _ -> "DRIFT        "
        putStrLn (tag ++ pad 28 section ++ " " ++ nm)
        case verdict of
          VExempt why -> putStrLn ("             " ++ why)
          VWaived why details ->
              mapM_ (putStrLn . ("             " ++)) (why : details)
          VDrift details ->
              mapM_ (putStrLn . ("             " ++)) details
          VOk -> return ()
        return verdict
    let nOK = length (filter isOk results)
        nDrift = length (filter isDrift results)
        nOther = length results - nOK - nDrift
    if (nDrift == 0)
      then do putStrLn ("tconcheck: " ++ show nOK ++ " entries OK"
                        ++ (if nOther > 0
                            then " (" ++ show nOther ++ " exempt/waived)"
                            else ""))
              exitWith ExitSuccess
      else do putStrLn ("tconcheck: DRIFT in " ++ show nDrift ++ " of "
                        ++ show (length results) ++ " entries")
              exitWith (ExitFailure 1)

pad :: Int -> String -> String
pad n s = s ++ replicate (n - length s) ' '
