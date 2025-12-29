{-# LANGUAGE CPP #-}
module ADropUndet(aDropUndet) where

import qualified Data.Map.Lazy as M
import Error(ErrMsg(..), ErrorHandle, bsErrorUnsafe, internalError)
import PPrint
import Position
import Backend
import ASyntax
import ASyntaxUtil
import IntLit(ilHex)
import IntegerUtil
import Flags
import Prim


-- During elaboration, undetermined values may have been annotated with
-- recommended values (but left as undetermined).  Here we replace them
-- with the recommended value.
--
-- For undetermined values without recommendations, we have two options:
-- leave it for the backend to optimize or pick a value now (so that all
-- backends see the same value, to produce identical simulation results).
-- This choice is specified by the user with the -opt-undetermined-vals flag.
-- If a value is picked, use to value given by the -unspecified-to flag.
--
-- This stage also applies an if-expr optimization [see XXX comments].
-- That is, if one branch of an if-expr is Undet, then it picks the value
-- to be the same as the other branch.  This is not safe to do when the
-- other branch contains the result of an ActionValue method or foreign
-- task, unless -opt-undetermined-vals is given.  (See the "canFixUndet"
-- function in ITransform, which is doing a simillar check).
--
aDropUndet :: ErrorHandle -> Flags -> APackage -> APackage
aDropUndet errh flags apkg =
    let defmap = M.fromList $
                   map (\d -> (adef_objid d, adef_expr d)) $
                     apkg_local_defs apkg
    in  mapAExprs (fixUndet errh flags defmap) apkg


fixUndet :: ErrorHandle -> Flags -> M.Map AId AExpr -> AExpr -> AExpr
fixUndet errh flags defmap = g
  where
        -- whether to pick values for undets without a recommended value
        b = optUndet flags
        -- the value that undets should be set to
        tgt = unSpecTo flags

        -- construct a map of whether each def contains an AVValue
        avmap :: M.Map AId Bool
        avmap = M.map (hasNoActionValue avmap) defmap

        -- recursively apply "f" to an expression
        g = exprMap f

        -- handle an expression
        f :: AExpr -> Maybe AExpr
        -- if the Undet has a recommended value, use it
        f (ASAny _ (Just e)) = Just (g e)
        -- if it doesn't, and the backends are not allowed to diverge,
        -- then replace it with a constant
        f (ASAny t Nothing) | (not b) = Just (mkUnspec errh tgt t)
        -- XXX This is a fixup for ITransform not picking the best value.
        -- XXX The long-term solution is to not pick values in ITransform,
        -- XXX but to wait until the Path Graph is available.
        f (APrim i t PrimIf [_, tt, ff]) =
            let tt'  = g tt
                ff'  = g ff
            in  case (tt,ff) of
                  ((ASAny _ _), _) | canFixUndet flags avmap ff' -> Just ff'
                  (_, (ASAny _ _)) | canFixUndet flags avmap tt' -> Just tt'
                  _ -> Nothing
        -- otherwise, don't change it
        f _ = Nothing


mkUnspec :: ErrorHandle -> String -> AType -> AExpr
mkUnspec errh tgt t =
    let sz = aSize t
        val = case tgt of
                "0" -> 0
                "1" -> (2^sz) -1
                "A" -> aaaa sz
                _   -> -- this situation should have been rejected when
                       -- we checked command-line flags
                       bsErrorUnsafe errh
                           [(noPosition, ENoOptUndetNoXZ tgt)]
    in
        ASInt defaultAId t (ilHex val)


canFixUndet :: Flags -> M.Map AId Bool -> AExpr -> Bool
canFixUndet flags avmap e =
    if (optUndet flags && (backend flags == Just Verilog))
    then True
    else hasNoActionValue avmap e

hasNoActionValue :: M.Map AId Bool -> AExpr -> Bool
hasNoActionValue avm (APrim { ae_args = es }) = all (hasNoActionValue avm) es
hasNoActionValue avm (AMethCall { ae_args = es }) = all (hasNoActionValue avm) es
hasNoActionValue avm (AMethValue {}) = False
hasNoActionValue avm (ATuple _ es) = all (hasNoActionValue avm) es
hasNoActionValue avm (ATupleSel { ae_exp = e }) = hasNoActionValue avm e
hasNoActionValue avm (ANoInlineFunCall { ae_args = es }) = all (hasNoActionValue avm) es
hasNoActionValue avm (AFunCall { ae_args = es }) = all (hasNoActionValue avm) es
hasNoActionValue avm (ATaskValue {}) = False
hasNoActionValue avm (ASPort {}) = True
hasNoActionValue avm (ASParam {}) = True
hasNoActionValue avm (ASDef { ae_objid = i }) =
    case (M.lookup i avm) of
      Just b -> b
      Nothing -> internalError ("hasNoActionValue: ASDef: " ++ ppReadable i)
hasNoActionValue avm (ASInt {}) = True
hasNoActionValue avm (ASReal {}) = True
hasNoActionValue avm (ASStr {}) = True
hasNoActionValue avm (ASAny { ae_val = Nothing }) = True
-- XXX if the recommended value has an AV, we could just drop it
hasNoActionValue avm (ASAny { ae_val = Just e }) = hasNoActionValue avm e
hasNoActionValue avm (ASClock {}) = True
hasNoActionValue avm (ASReset {}) = True
hasNoActionValue avm (ASInout {}) = True
hasNoActionValue avm (AMGate {}) = True
