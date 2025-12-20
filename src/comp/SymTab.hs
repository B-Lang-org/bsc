{-# LANGUAGE CPP #-}
module SymTab(
              SymTab(..), VarInfo(..), TypeInfo(..),
              ConInfo(..), ConTagInfo(..),
              FieldInfo(..), VarKind(..),
              getAllTypes,
              emptySymtab,
              addVars, addTypes, addCons, addFields, addClasses,
              addVarsUQ, addTypesUQ, addClassesUQ, mkDefaultQuals,
              addTypesQ, addFieldsQ,
              findVar, findCon, findConVis, findType,
              findField, findFieldVis, findSClass, mustFindClass,
              findFieldInfo,
              getMethodArgNames, getIfcFieldNames, getIfcFlatMethodNames
              ) where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import Data.List(find)
import Data.Maybe(isNothing, isJust)
import qualified Data.Map as M
import Eval(NFData(..), rnf7)
import PPrint
import Id
import Pred(Class(..))
import Assump
import Scheme(Scheme(..))
import Pred(Qual(..))
import CType
import Type(isClock, isReset, isInout)
import CSyntax(CClause)
import Pragma
import ConTagInfo

import ErrorUtil(internalError)

--import Debug.Trace

type IdMap a = M.Map Id a

data VarInfo
        -- the Maybe is whether the identifier has been deprecated, and why
        = VarInfo !VarKind !Assump !(Maybe String)
        deriving (Show)

instance PPrint VarInfo where
    pPrint d p (VarInfo k a m) =
        pparen (p>0) $
            text "VarInfo" <+> pPrint d 1 k <+> pPrint d 1 a <+>
            pPrint d 1 (isJust m)

data VarKind
        = VarPrim
        | VarDefn
        | VarMeth
        -- the maybe [String] is portlist for Verilog foreign funcs as modules
        -- (as "noinline" compiles to)
        | VarForg String (Maybe ([String], [String]))
        deriving (Show)

instance PPrint VarKind where
    pPrint _ _ k = text (show k)

data ConInfo
        = ConInfo { ci_id :: Id,
                    ci_visible :: Bool,
                    ci_assump :: Assump,    -- type
                    ci_taginfo :: ConTagInfo -- constructor number and tag metadata
                  }
        deriving (Show, Eq)

-- test whether two ConInfo are identical except for the visibility
conInfoEq :: ConInfo -> ConInfo -> Bool
conInfoEq ci1 ci2 =
    (ci1 { ci_visible = False }) == (ci2 { ci_visible = False })

-- merge two coninfo lists, overriding hidden entries with visible entries
conInfoMerge :: [ConInfo] -> [ConInfo] -> [ConInfo]
conInfoMerge new_cis old_cis = foldr mergeFn old_cis new_cis
    where mergeFn ci [] = [ci]
          mergeFn ci (h:rest) =
              if (conInfoEq h ci)
              then if (ci_visible h) then (h:rest) else (ci:rest)
              else (h : mergeFn ci rest)

instance NFData ConInfo where
    rnf x = seq x ()

instance PPrint ConInfo where
    pPrint d p (ConInfo i vis a cti) = pparen (p>0) $ text "ConInfo" <+> pPrint d 1 i <> pVis vis <+> pPrint d 1 a <+> pPrint d 1 cti
        where pVis False = text " (invisible)"
              pVis True = text " (visible)"

data TypeInfo
        = TypeInfo {
              ti_qual_id   :: (Maybe Id),  -- Nothing for numeric and string types
              ti_kind      :: Kind,
              ti_type_vars :: [Id],
              ti_sort      :: TISort
          } deriving (Show)

instance PPrint TypeInfo where
    pPrint d p (TypeInfo _ k _ ti) = pparen (p>0) $ text "TypeInfo" <+> pPrint d 10 k <+> pPrint d 1 ti

data FieldInfo
        = FieldInfo {
                     fi_id      :: Id ,  -- Id is the identifier of a type which has this field
                     fi_visible :: Bool, -- Bool is if the fields of that type are visible to user
                     fi_arity   :: Int,  -- Int is the arity of the type
                     fi_assump  :: Assump,
                     fi_pragmas :: [IfcPragma],
                     fi_default :: [CClause],
                     fi_orig_type :: Maybe CType -- original field type for wrapped fields
                    }
        deriving (Show)

-- test whether two FieldInfo are identical except for the visibility
fieldInfoEq :: FieldInfo -> FieldInfo -> Bool
fieldInfoEq fi1 fi2 =
    ((fi_id fi1) == (fi_id fi2)) &&
    -- ignore fi_visible
    ((fi_arity fi1) == (fi_arity fi2)) &&
    ((fi_assump fi1) == (fi_assump fi2)) &&
    ((fi_pragmas fi1) == (fi_pragmas fi2)) &&
    -- ignore fi_default
    ((fi_orig_type fi1) == (fi_orig_type fi2))

-- merge two coninfo lists, overriding hidden entries with visible entries
fieldInfoMerge :: [FieldInfo] -> [FieldInfo] -> [FieldInfo]
fieldInfoMerge new_fis old_fis = foldr mergeFn old_fis new_fis
    where mergeFn fi [] = [fi]
          mergeFn fi (h:rest) =
              if (fieldInfoEq h fi)
              then if (fi_visible h) then (h:rest) else (fi:rest)
              else (h : mergeFn fi rest)

instance PPrint FieldInfo where
    pPrint d p (FieldInfo i _ n a ps def_cs mot) =
        pparen (p>0) $
          text "FieldInfo" <+>
          pPrint d 1 i <+>
          pPrint d 1 n <+>
          pPrint d 1 a $+$
          text ( "Fields:" ) <> pPrint d 2 ps <>
          (case (def_cs) of
               [] -> empty
               cs -> text ( "Default: ") <> pPrint d 0 cs) <>
          (case (mot) of
               Nothing -> empty
               Just t -> text ("Original type: ") <> pPrint d 0 t)

instance NFData FieldInfo where
    rnf (FieldInfo a b c d e f g) = rnf7 a b c d e f g


-- The symbol table is composed of several other tables
data SymTab =
        S (IdMap VarInfo) (IdMap [ConInfo]) (IdMap TypeInfo) (IdMap [FieldInfo]) (IdMap Class)
          -- The TypeInfo is indexed by type and returns the info for that type
          --   (indexed generally by both qualified and unqualified name)
          -- The FieldInfo is indexed by field id (e.g., "_write" returns the fields of Reg)
          --   or by superclass (e.g. Literal returns the superclasses of "Arith")

instance Eq SymTab where -- just because we need one for forcing evaluation
    _ == _ = False

showsPrecList :: Show a => Int -> [a] -> String -> String
showsPrecList wid (thing@[_]) z =
    concat ( sps wid thing ) ++ z

showsPrecList wid (thing@(_)) z =
     (showsPrec wid thing . showString "\n") z

sps :: Show a => Int -> [a] -> [String]
sps wid islist =
    [ show thing ++ "\n" | thing <- islist ]

instance Show SymTab where
    showsPrec _ (S v c t f cl) =
        showString "Vars: " . showsPrecList 0 (M.toList v) . showString "\n" .
        showString "Cons: " . showsPrecList 0 (M.toList c) . showString "\n" .
        showString "Types: " . showsPrecList 0 (M.toList t) . showString "\n" .
        showString "Fields: " . showsPrecList 0 (M.toList f) . showString "\n" .
        showString "Classes: " . showsPrecList 0 (M.toList cl) . showString "\n"

instance PPrint SymTab where
    pPrint d _ (S v c t f cl) =
        (text "Vars:" <+> pPrint d 0 (M.toList v) ) $+$
        (text "Cons:" <+> pPrint d 0 (M.toList c) ) $+$
        (text "Types:" <+> pPrint d 0 (M.toList t) ) $+$
        (text "Fields:" <+> pPrint d 0 (M.toList f) ) $+$
        (text "Classes:" <+> pPrint d 0 (M.toList cl) )

instance NFData SymTab where
    rnf x = ()                -- XXX

emptySymtab :: SymTab
emptySymtab = S M.empty M.empty M.empty M.empty M.empty

-- ---------------

-- mkQuals applied to identifier returns a list of forms of that identifier
-- which should be added to the symbol table (qual, unqual, re-qual)
addVars :: (Id -> [Id]) -> SymTab -> [(Id, VarInfo)] -> SymTab
addVars mkQuals (S v c t f cl) ivs =
    S (foldr (uncurry M.insert) v (addQuals mkQuals ivs)) c t f cl

-- mkQuals applied to identifier returns a list of forms of that identifier
-- which should be added to the symbol table (qual, unqual, re-qual)
addTypes :: (Id -> [Id]) -> SymTab -> [(Id, TypeInfo)] -> SymTab
addTypes mkQuals (S v c t f cl) its =
    S v c (foldr (uncurry (M.insertWith pickBetter)) t (addQuals mkQuals its)) f cl
  where
    -- replace an abstract export with a full export
    pickBetter it1 it2 =
        case (ti_sort it1, ti_sort it2) of
          -- are these needed?
          (TIabstract, TIabstract) -> it1
          (TIabstract, _)          -> it2
          -- abstract typeclasses have hidden methods, but might still
          -- have superclasses (so the list is not necessarily null)
          (TIstruct SClass fs1, TIstruct SClass fs2)
            | length fs2 > length fs1 -> it2
          _ -> it1

-- mkQuals applied to identifier returns a list of forms of that identifier
-- which should be added to the symbol table (qual, unqual, re-qual)
addCons :: (Id -> [Id]) -> SymTab -> [(Id, ConInfo)] -> SymTab
addCons mkQuals (S v c t f cl) ics =
    let
        insertFn (i,c) = M.insertWith conInfoMerge i [c]
        c' = foldr insertFn c (addQuals mkQuals ics)
    in
        S v c' t f cl

-- mkQuals applied to identifier returns a list of forms of that identifier
-- which should be added to the symbol table (qual, unqual, re-qual)
addFields :: (Id -> [Id]) -> SymTab -> [(Id, FieldInfo)] -> SymTab
addFields mkQuals (S v c t f cl) ifs =
    let
        insertFn (i,f) = M.insertWith fieldInfoMerge i [f]
        f' = foldr insertFn f (addQuals mkQuals ifs)
    in
        S v c t f' cl

-- mkQuals applied to identifier returns a list of forms of that identifier
-- which should be added to the symbol table (qual, unqual, re-qual)
addClasses :: (Id -> [Id]) -> SymTab -> [Class] -> SymTab
addClasses mkQuals (S v c t f cl) cls =
    S v c t f
          (foldr (uncurry M.insert) cl (addQuals mkQuals (map (\c -> (typeclassId $ name c, c)) cls)))

-- -----

-- given:
--  * a pairing of an Id with its symbol info
--  * mkQuals, a function which makes a list of the Ids under which this
--    entry should be recorded (usually just the original qual Id, possibly
--    the unqual Id, and maybe a re-qualified Id if its a re-export)
-- returns:
--  a list of pairings of the Ids with the symbol info
addQuals :: (Id -> [Id]) -> [(Id, a)] -> [(Id, a)]
addQuals mkQuals ixs = concatMap addQuals' ixs
    where addQuals' pair@(name, value) =
              [ (i, value) | i <- mkQuals name ]

-- ---------------

-- versions which add both qual and unqual names
addTypesUQ :: SymTab -> [(Id, TypeInfo)] -> SymTab
addTypesUQ   = addTypes mkDefaultQuals

addVarsUQ :: SymTab -> [(Id, VarInfo)] -> SymTab
addVarsUQ  = addVars mkDefaultQuals

addClassesUQ :: SymTab -> [Class] -> SymTab
addClassesUQ = addClasses mkDefaultQuals

-- For Ids which should be entered as both qualified and unqualified
mkDefaultQuals :: Id -> [Id]
mkDefaultQuals name =
    -- if the Id is already unqualified, don't duplicate it
    if (isNothing (getIdQFString name))
    then [name]
    else [unQualId name, name]

-- -----

-- versions which only add the name as it is (qualified)
addTypesQ :: SymTab -> [(Id, TypeInfo)] -> SymTab
addTypesQ  = addTypes mkSameQual
addFieldsQ :: SymTab -> [(Id, FieldInfo)] -> SymTab
addFieldsQ = addFields mkSameQual

-- For Ids which should be entered as-is
mkSameQual :: Id -> [Id]
mkSameQual name = [name]

-- ---------------

findVar :: SymTab -> Id -> Maybe VarInfo
findVar (S v _ _ _ _) i = --trace (ppReadable (show i, show (map fst (M.toList v)))) $
        M.lookup i v

findCon :: SymTab -> Id -> Maybe [ConInfo]
findCon (S _ c _ _ _) i = M.lookup i c

findConVis :: SymTab -> Id -> Maybe [ConInfo]
findConVis s i = fmap (filter ci_visible) (findCon s i)

findType :: SymTab -> Id -> Maybe TypeInfo
findType (S _ _ t _ _) i = M.lookup i t

findField :: SymTab -> Id -> Maybe [FieldInfo]
findField (S _ _ _ f _) i = M.lookup i f

findFieldVis :: SymTab -> Id -> Maybe [FieldInfo]
findFieldVis s i = fmap (filter fi_visible) (findField s i)

findSClass :: SymTab -> CTypeclass -> Maybe Class
findSClass (S _ _ _ _ cl) (CTypeclass i) = M.lookup i cl

mustFindClass :: SymTab -> CTypeclass -> Class
mustFindClass r i =
    case findSClass r i of
     Just cl -> cl
     Nothing -> internalError ("mustFindClass " ++ show i)

getAllTypes :: SymTab -> [(Id, TypeInfo)]
getAllTypes (S _ _ t _ _) = M.toList t

-- a double key lookup into the symbol table to get field names of an interface method
-- The first key is the interface name, the second the method name.
findFieldInfo :: SymTab -> Id -> Id -> Maybe FieldInfo
findFieldInfo symtable ifcName methodName =
      -- There may be multiple types with the same field, and the types
      -- may even have the same name, so we need to do the lookup using
      -- the qualified type name
      if (isUnqualId ifcName)
      then internalError ("findFieldInfo: unqualified ifcName: " ++
                          ppReadable ifcName)
      else fieldInfo
    where
      -- extra field info from symbol table for matching names
      fields    = findField symtable methodName
      fieldInfo = case fields of
                  Just fieldInfos -> find matches fieldInfos
                  _               -> Nothing
      -- find function equality test for in ifcName lookup
      matches (FieldInfo {fi_id = ifcId }) = (ifcId == ifcName)


getMethodArgNames :: SymTab -> Id -> Id -> [Id]
getMethodArgNames symtable ifcId methId =
    case (findFieldInfo symtable ifcId methId) of
        Nothing -> []
        Just finfo -> filterIArgNames (fi_pragmas finfo)

getIfcFieldNames :: SymTab -> Id -> [Id]
getIfcFieldNames symbolTable ifcId = fields
    where
    fields = case findType symbolTable ifcId of
             Nothing ->  []
             Just (TypeInfo (Just ti) _ _ (TIstruct ss fs)) | isIfc ss -> fs
             Just x -> []

-- generate just the method names, following subinterfaces
getIfcFlatMethodNames :: SymTab -> Id -> [Id]
getIfcFlatMethodNames symt topIfcId =
  let
      fields :: Id -> Maybe [Id]
      fields conId =
          case findType symt conId of
            Nothing -> internalError ("getIfcFlatMethodNames: findType: " ++
                                      ppReadable conId)
            Just (TypeInfo (Just ti) _ _ (TIstruct ss fs))
                | isIfc ss -> Just fs
            Just x         -> Nothing

      recurseFn :: [Id] -> Id -> Id -> [Id]
      recurseFn pfx ifcId fieldId =
        let pfx' = pfx ++ [fieldId]
            meth_res = [flattenUSId pfx']
        in  case findFieldInfo symt ifcId fieldId of
              Nothing -> internalError ("getIfcFlatMethodNames: " ++
                                        ppReadable fieldId)
              Just (FieldInfo { fi_assump = (_ :>: Forall _ (_ :=> t)) }) ->
                  case (getArrows t) of
                    -- fields always have the ifc as the first argument
                    ([], _) -> internalError
                                   ("getIfcFlatMethodNames: type: " ++
                                    ppReadable (fieldId, t))
                    -- ignore non-method fields
                    ([_], res) | (isClock res || isReset res || isInout res)
                            -> []
                    -- if it's an ifc, recurse;
                    -- if it's a method, return its name
                    ([_], res) ->
                        case (leftCon res) of
                          Nothing -> meth_res
                          Just conId ->
                              case (fields conId) of
                                Nothing -> meth_res
                                Just fs -> concatMap (recurseFn pfx' conId) fs
                    -- if it has more arguments, it's just a method
                    (_, _) -> meth_res

      topFields =
          case (fields topIfcId) of
            Just fs -> fs
            Nothing -> internalError ("getIfcFlatMethodNames: not ifc: "
                                      ++ ppReadable topIfcId)
  in
      concatMap (recurseFn [] topIfcId) topFields
