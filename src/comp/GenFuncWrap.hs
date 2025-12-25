module GenFuncWrap(genFuncWrap, addFuncWrap,
                   makeGenFuncId
                  ) where

import Data.Maybe(isJust)
import Data.List(unzip4, partition)
import FStringCompat
import Error(internalError, ErrMsg(..), ErrorHandle, bsError)
import Flags(Flags)
import PPrint
import Id
import PreIds(idBits, idUnpack, idPack, tmpVarIds,
              idActionValue, idFromActionValue_)
import CSyntax
import SymTab
import Scheme
import Assump
import Type(tModule, fn)
import CType(getArrows, cTVarNum)
import Pred(expandSyn)
import TypeCheck(cCtxReduceDef)
import Subst(tv)
import Util(concatMapM)
import Pragma
-- import Util(traces)
import GenWrapUtils

-- ===============

-- naming convention

makeGenFuncId :: Id -> Id
makeGenFuncId i = mkIdPre (mkFString "module_") i

-- ===============

-- information that is returned from the call to genFuncWrap,
-- to be passed to the later call to addFuncWrap

type FuncInfo = (Id, Id, Id, [Id], CQType)

-- ===============

-- Find all functions tagged as "noinline" and generate module and
-- interface declarations for them.  Returns:
--  * update CPackage with the new defs (and Pnoinline pragmas removed)
--  * new symbol table (with info about the new ifcs)
--  * FuncInfo about the noinline functions, to be used by a later
--    call to addFuncWrap
--
genFuncWrap :: ErrorHandle -> Flags -> Bool -> CPackage -> SymTab ->
               IO (CPackage, SymTab, [FuncInfo])
genFuncWrap errh flags False p s = return (p, s, [])
genFuncWrap errh flags True (CPackage pkgId exps imps impsigs fixs ds includes) symt = do
    let
        -- separate out the noinline pragmas
        (fpragmas, ds_no_fpragmas) = partition isNoInline ds
            where isNoInline (CPragma (Pnoinline _)) = True
                  isNoInline _ = False

        -- Ids of functions specified as "noinline"
        fs = [ i | CPragma (Pnoinline is) <- fpragmas, i <- is ]

        -- update function:
        -- for noinline defs, call wrapFun to create updated defs and
        -- symbol table info.  for other defs, just return the def
        -- with no new symbol table info.
        wrap (CValueSign d@(CDef i _ _)) | i `elem` fs =
            ctxReduce errh flags symt d >>= wrapFun errh pkgId
        wrap d = return ([d], [], [], [])

    -- generate funcwrap info for all defs (minus the noinline pragmas)
    (dss, tss, fss, iss) <- mapM wrap ds_no_fpragmas >>= return . unzip4

    let
        ts = concat tss
        -- need to add the qualified versions of the types as well
        qts = [(qualId pkgId i, ti) | (i, ti) <- ts]

        -- XXX genWrap doesn't add qualified fields, so we don't either

        -- the new defs for the CPackage
        ds' = concat dss

        -- the new symbol table
        -- only add the names as they are (qualified)
        symt' = addFieldsQ
                  (addTypesQ symt (ts ++ qts)) (concat fss)

    return $
        (CPackage pkgId exps imps impsigs fixs ds' includes, symt', concat iss)

-- ---------------

ctxReduce :: ErrorHandle -> Flags -> SymTab -> CDef -> IO CDef
ctxReduce errh flags symt d =
    case (cCtxReduceDef flags symt (CValueSign d)) of
        Left msgs -> bsError errh msgs
        Right (CValueSign d') -> return d'
        Right dn -> internalError ("GenFuncWrap ctxReduce: " ++
                                   "unexpected defn: " ++ ppReadable dn)

-- ---------------

-- For each def, generate a 4-tuple of information
--  * new top-level defs: ifc, generate pragma, module
--  * new entries for typeinfo table: (ifc id, ifc type)
--  * new entried for fieldinfo table: (ifc id, ifc fields)
--  * funcinfo, to be passed later to addFuncWrap
--
wrapFun :: ErrorHandle -> Id -> CDef ->
           IO ([CDefn], [(Id, TypeInfo)], [(Id, FieldInfo)], [FuncInfo])
wrapFun errh pkgId d@(CDef i qt@(CQType [] t) cs) =
    -- traces( "GenFuncWrap::wrapFun: d " ++ ppReadable d ) $
    let
        -- position of the function, for transferring to the new defs
        pos = getIdPosition i

        -- propagate arguments names, if possible
        -- XXX names are a little uglier for classic defs
        -- XXX do we need to propagate type-info as well?
        argNames = map fst (getDefArgs cs t)

        -- ----------
        -- generate a new interface

        -- name of the new ifc
        ifcId = mkIdPre (mkFString "Interface_") i
        ifcQId = qualId pkgId ifcId
        -- type of the new ifc
        ifcTy = TCon (TyCon ifcQId (Just KStar)
                         (TIstruct (SInterface noIfcPragmas) [i]))
        -- type info for the new ifc
        ifcInf = TypeInfo (Just ifcQId) KStar []
                     (TIstruct (SInterface noIfcPragmas) [i])
                     Nothing

        -- pragmas for the method
        field_pragmas = [PIArgNames argNames]

        -- defn for the new ifc
        ifc = Cstruct True (SInterface noIfcPragmas) (IdKind ifcId KStar) []
              [CField { cf_name = i,
                        cf_pragmas = Just field_pragmas,
                        cf_type = qt,
                        cf_default= [],
                        cf_orig_type = Nothing }] []

        -- Fieldinfo for the method of the new ifc
        fldInf = FieldInfo ifcQId True 0
                     (i :>: toScheme (ifcTy `fn` t))
                     field_pragmas
                     [] -- no defaults
                     Nothing -- no type for wrapper tracking
                     Nothing

        -- ----------
        -- generate a new module, providing that interface

        -- name of the new module
        modId = makeGenFuncId i
        -- expr for the new module
        mode = Cmodule pos
                   [CMinterface (Cinterface pos Nothing [CLValueSign d []])]
        -- defn for the new module
        mod = CValueSign (CDef modId (CQType [] (TAp tModule ifcTy))
                             [CClause [] [] mode])
        -- pragma indicating to generate this new module
        gen = CPragma (Pproperties modId [PPverilog])
    in
      if (not (null (tv t)))
      then bsError errh [(getPosition i, ENoInlinePolymorphic (getIdString i))]
      else return $
        (
        -- new top-level defs
        [ifc, gen, mod],
        -- ifc Id and type info (for the symbol table)
        [(ifcId, ifcInf)],
        -- method Id and field info (for the symbol table)
        [(i, fldInf)],
        --
        [(modId, ifcId, i, argNames, qt)]
        )

wrapFun errh _ (CDef i _ _) =
    bsError errh [(getPosition i, ENoInlineContext (getIdBaseString i))]

-- this is an internal error, because only the typechecker creates CDefT
wrapFun errh _ (CDefT i _ _ _) =
    internalError ("wrapFun: context CDefT not allowed for verilog function: "
                      ++ ppString i)


-- ===============

-- This is called after GenWrap, purely to let GenWrap do the work
-- of creating the primitive interface for the function (bitified, etc).
-- Then this code looks up the interface to get the new types and
-- constructs the defs for the "foreign" declaration and a wrapper that
-- packs to / unpacks from the primitive form.

addFuncWrap :: ErrorHandle -> SymTab -> [FuncInfo] -> CPackage -> IO CPackage
addFuncWrap _ _ [] p = return p
addFuncWrap errh symt is (CPackage modid exps imps impsigs fixs ds includes) = do
    is' <- concatMapM addf is
    return $ CPackage modid exps imps impsigs fixs (ds ++ is') includes
  where
    addf :: FuncInfo -> IO [CDefn]
    addf (mi, ti, i, args, qt) =
        let
            -- escaped versions of the func name and type
            -- (as would be generated by GenWrap)
            i_ = modIdRename [] i
            ti_ = ifcIdRename [] ti

            -- find the declaration for the escapted interface
            -- which GenWrap created (in primitive bitified form)
            -- and extract the types of the methods
            method_types =
                [ cf_type field
                      | Cstruct _ _ (IdKind ti_' _) _ fs _ <- ds,
                        ti_ == ti_', field <- fs, cf_name field == i ]
        in
            -- exactly one method should be found
            case (method_types) of
                [qt_@(CQType _ t_)] -> do
                      let -- the number of arguments
                          n = nArrows t_
                      -- definitions for the wrapper and wrappee
                      d <- funcDef errh symt i qt i_ n qt_
                      let d_ = funcDef_ mi i i_ qt_ args
                      return [d, d_]
                _ -> internalError ("addFuncWrap: " ++ ppString (ti_, i_))

-- ---------------

-- make the wrapper definition (with the original function id)
-- which packs the arguments to and unpacks the results from
-- the foreign function (with an escaped id).
--   i  = the original function id
--   oqt = qualified type of the original function
--   i_ = the escaped id (declared as foreign)
--   n  = the number of arguments to the foreign function
--   t  = the base type of the foreign function
funcDef :: ErrorHandle -> SymTab -> Id -> CQType -> Id -> Int -> CQType -> IO CDefn
funcDef errh symt i oqt@(CQType octxs ot) i_ n (CQType _ t) =
    let
        -- unfortunately, we have to duplicate the work that genwrap did
        -- in creating the interface interface type and interface
        -- conversion functions

        pos = getPosition i
        (as, r) = getArrows ot

        -- the arguments are always bitifiable
        bitsCtx a s = CPred (CTypeclass idBits) [a, s]
        size_vars =  map (cTVarNum . enumId "sn" pos) [0..]
        as_ctxs = zipWith bitsCtx as size_vars

        vs = map (setIdPosition pos) $ take n tmpVarIds
        epack e = cVApply idPack [e]
        es = map (epack . CVar) vs

        f_expr = cVApply i_ es

        -- the result is either an actionvalue or a value
        isAV = isActionValue symt r

        r_size_var = cTVarNum $ enumId "sn" pos n
        r_ctxs = case (isAV) of
                     Just av_t -> [bitsCtx av_t r_size_var]
                     Nothing   -> [bitsCtx r    r_size_var]

        expr = if (isJust isAV)
               then cVApply idFromActionValue_ [f_expr]
               else cVApply idUnpack           [f_expr]

        -- put the ctxs together
        ctxs' = as_ctxs ++ r_ctxs ++ octxs
        qt'   = CQType ctxs' ot
    in
        -- XXX this code works for Action/ActionValue foreign funcs,
        -- XXX but they are not handled by astate yet
        if (isJust isAV)
        then bsError errh [(getPosition i, ENoInlineAction (getIdBaseString i))]
        else return $
             CValueSign (CDef i qt' [CClause (map CPVar vs) [] expr])

-- ---------------

-- make the foreign function declaration (with escaped id) to be wrapped.
--   mi   = the combinational module to instantiate
--   i_   = the escaped identifier to use for the foreign declaration
--   i    = the original identifier, which also happens to be the
--          name of the method on the module, which is the prefix for
--          the port names for the method (used to generate the port names)
--   qt_  = the qualified type of the wrapped function
--          (this has been bitified by GenWrap)
--   args = List of function args
funcDef_ :: Id -> Id -> Id -> CQType -> [Id] -> CDefn
funcDef_ mi i i_ qt_ args =
    let
        mstr = getIdString mi
        -- input ports: <methId>_<argId>
        iports = [ oport ++ "_" ++ getIdString arg | arg <- args ]
        -- output port: <methId>
        oport = getIdString i
    in
        Cforeign i_ qt_ (Just mstr) (Just (iports, [oport]))

-- ---------------

nArrows :: Type -> Int
nArrows t = length $ fst $ getArrows t

-- ===============

-- utilities copied from GenWrap, but are not monadic here, because
-- the symbol table comes in as a parameter (not as monad state)

-- expand type aliases and apply type functions
expandSynSym :: SymTab -> Type -> Type
expandSynSym symt xt =
   expandSyn (updTypes symt xt)
 where
   updTypes r o@(TCon (TyCon i _ TIabstract)) =
     case findType r i of
       Just (TypeInfo (Just i') k _ ti _) -> TCon (TyCon i' (Just k) ti)
       Just (TypeInfo Nothing _ _ _ _) ->
        internalError ("genFuncWrap: expandSynSym: unexpected numeric type:"
                          ++ ppReadable i)
       Nothing -> o
   updTypes r (TAp f a) = TAp (updTypes r f) (updTypes r a)
   updTypes r t = t


isActionValue :: SymTab -> Type -> Maybe Type
isActionValue symt t =
    case (expandSynSym symt t) of
        (TAp (TCon (TyCon i _ _)) av_t) | (qualEq i idActionValue)
          -> Just av_t
        _ -> Nothing

-- ===============
