module VStableRenumber(stableRenumberVProgram) where

import Data.Char(isDigit)
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Generics(everywhere, mkT, listify)

import Id(setIdBaseString)
import Verilog

-- Under -stable-verilog, renumber the compiler-generated name families
--
--     <stem>___dN   (backend def temporaries)
--     <stem>__hN    (elaboration heap ids, minted into the .ba)
--     <stem>__qN    (Verilog-quirks temporaries)
--
-- per module, by order of first occurrence in the emitted structure,
-- so the numbers are a pure function of the module's contents rather
-- than of mint order.  Mint order varies with compile history (the
-- heap ids arrive in the .ba with their elaboration-time numbers, and
-- the backend counters run in traversal order), so without this pass
-- two compiles that agree on structure can still disagree on N.
--
-- Soundness:
--  * Renaming is a per-module simultaneous substitution.  A target
--    name <stem><marker><k> can only collide with another family
--    member -- any name matching the pattern is itself in the map --
--    and family members all move at once.  Targets that would collide
--    with a non-renameable name (below) are skipped over.
--  * Names in non-renameable positions are never collected and never
--    produced as targets: the module's own name, everything in the
--    port list, instantiated module names, instance names, and the
--    formal port/parameter keys of instantiations (they belong to the
--    child module).  If a family-shaped name also occurs in such a
--    position (a user port named x__h5), the whole name is left
--    untouched to avoid capture.
--  * This runs before removeDollarsFromVerilog; generated family
--    names never contain '$', so the passes are disjoint.

stableRenumberVProgram :: VProgram -> VProgram
stableRenumberVProgram (VProgram ms dpis cs) =
    VProgram (map renumberModule ms) dpis cs

data Family = FamD | FamH | FamQ | FamF | FamDM | FamDS
    deriving (Eq, Ord)

markerText :: Family -> String
markerText FamD  = "___d"
markerText FamH  = "__h"
markerText FamQ  = "__q"
markerText FamF  = "__f"   -- ANoInline instance-connection wires
markerText FamDM = "_dm"   -- AOpt-minted names (whole name, no stem)
markerText FamDS = "_ds"   -- Synthesize-minted names (whole name, no stem)

-- whether the family's names are the bare marker plus number
-- (no stem before the marker)
stemlessOK :: Family -> Bool
stemlessOK FamDM = True
stemlessOK FamDS = True
stemlessOK _     = False

-- split a name into (stem, family, number-text) at the rightmost
-- marker-followed-by-digits suffix
matchFamily :: String -> Maybe (String, Family)
matchFamily s =
    let (rds, rrest) = span isDigit (reverse s)
        rest = reverse rrest
        try fam = let m = markerText fam
                      lm = length m
                      (pre, suf) = splitAt (length rest - lm) rest
                  in  if suf == m && (stemlessOK fam || not (null pre))
                      then Just (pre, fam)
                      else Nothing
    in  if null rds
        then Nothing
        else case [ r | Just r <- map try [FamD, FamH, FamQ, FamF, FamDM, FamDS] ] of
               (r : _) -> Just r
               []      -> Nothing

renumberModule :: VModule -> VModule
renumberModule vm =
    let
        isVId :: VId -> Bool
        isVId _ = True

        vidStr :: VId -> String
        vidStr (VId s _ _) = s

        -- names that must not change (or be created by renaming)
        instFixed :: VMItem -> [String]
        instFixed (VMInst m i pas pos) =
            [vidStr m, vidStr i] ++
            either (const []) (map (vidStr . fst)) pas ++
            map (vidStr . fst) pos
        instFixed (VMComment _ it)      = instFixed it
        instFixed (VMRegGroup _ _ _ it) = instFixed it
        instFixed (VMGroup _ itss)      = concatMap (concatMap instFixed) itss
        instFixed _                     = []

        -- foreign linkage names must never change: the function/task
        -- names of foreign calls (DPI declarations live at file scope,
        -- outside this module walk)
        -- (a user's imported function may itself be family-shaped,
        -- e.g. import \"BDPI\" f__h1)
        isFctName :: VExpr -> [String]
        isFctName (VEFctCall f _) = [vidStr f]
        isFctName _               = []

        foreignFixed :: [String]
        foreignFixed =
            concatMap isFctName (listify (\e -> case e of
                                                  VEFctCall _ _ -> True
                                                  _             -> False)
                                         (vm_body vm)) ++
            [ vidStr t | VTask t _ <- listify (\st -> case st of
                                                        VTask _ _ -> True
                                                        _         -> False)
                                              (vm_body vm) ]

        excluded :: S.Set String
        excluded = S.fromList (
            vidStr (vm_name vm) :
            [ s | VId s _ _ <- listify isVId (vm_ports vm) ] ++
            foreignFixed ++
            concatMap instFixed (vm_body vm))

        -- family members in order of first occurrence in the body
        occurrences :: [String]
        occurrences = [ s | VId s _ _ <- listify isVId (vm_body vm) ]

        firstSeen :: S.Set String -> [String] -> [(String, String, Family)]
        firstSeen _ [] = []
        firstSeen seen (s : ss)
            | s `S.member` seen
            = firstSeen seen ss
            | not (s `S.member` excluded),
              Just (stem, fam) <- matchFamily s
            = (s, stem, fam) : firstSeen (S.insert s seen) ss
            | otherwise
            = firstSeen (S.insert s seen) ss

        members :: [(String, String, Family)]  -- (name, stem, family)
        members = firstSeen S.empty occurrences

        -- assign numbers per family in first-occurrence order,
        -- skipping targets that collide with non-renameable names
        assign :: M.Map Family Integer -> [(String, String, Family)]
               -> [(String, String)]
        assign _ [] = []
        assign ks ((nm, stem, fam) : rest) =
            let next n = let tgt = stem ++ markerText fam ++ show n
                         in  if tgt `S.member` excluded
                             then next (n + 1)
                             else (n, tgt)
                (k, target) = next (M.findWithDefault 1 fam ks)
            in  (nm, target) : assign (M.insert fam (k + 1) ks) rest

        renames :: M.Map String String
        renames = M.fromList [ (nm, tgt) | (nm, tgt) <- assign M.empty members
                                         , nm /= tgt ]

        subst :: VId -> VId
        subst v@(VId s i info) =
            case M.lookup s renames of
              Just s' -> VId s' (setIdBaseString i s') info
              Nothing -> v
    in
        if M.null renames
        then vm
        else vm { vm_body = everywhere (mkT subst) (vm_body vm) }
