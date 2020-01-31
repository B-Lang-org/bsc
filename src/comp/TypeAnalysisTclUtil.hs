{-# LANGUAGE ScopedTypeVariables #-}
module TypeAnalysisTclUtil
    (
     typeAnalysisToHTclObj,
     typeAnalysisToBitify,
     typeAnalysisToDetail,

     -- for displaying subparts
     structFieldToDetail,
     unionTagToDetail,
     typeAnalysisShort,
     showWidth,
     interfaceFieldToDetail
    ) where


import HTcl
import TclUtils
import TypeAnalysis

import PFPrint
import Id
import PreIds
import CType
import Pred
import Pragma

import Util(intercalate)
import Data.List(sort)
import IntegerUtil(integerToString)

-- ---------------

typeAnalysisToHTclObj :: TypeAnalysis -> HTclObj
typeAnalysisToHTclObj (Unknown) = TStr "Unknown"
typeAnalysisToHTclObj (Variable) = TStr "Variable"
typeAnalysisToHTclObj (Function) = TStr "Function"
typeAnalysisToHTclObj (Numeric) = TStr "Numeric"
typeAnalysisToHTclObj (Primary t k vs isC mwidth) =
    tag "Primary" $
        [TStr $ showType True t k vs] ++
	showPolymorphic isC ++
	showWidth mwidth
typeAnalysisToHTclObj (Vector isC len el mwidth) =
    tag "Vector" $
        [TStr $ showType True idVector kVector vsVector] ++
        showPolymorphic isC ++
	[tagStr "length" (pvStr len)] ++
	[tagStr "elem" (pvStr el)] ++
	showWidth mwidth
typeAnalysisToHTclObj (List isC el) =
    tag "List" $
        [TStr $ showType True idList kList vsList] ++
        showPolymorphic isC ++
	[tagStr "elem" (pvStr el)]
typeAnalysisToHTclObj (Alias t k vs atype) =
    tag "Alias" $
        [TStr $ showType True t k vs,
	 TStr (pvStr atype)] ++
	showTaggedPosition t
typeAnalysisToHTclObj (Struct t k vs isC fs mwidth) =
    tag "Struct" $
        [TStr $ showType True t k vs] ++
	showPolymorphic isC ++
	[tagLst "members" (map structFieldToHTclObj fs)] ++
	showWidth mwidth ++
	showTaggedPosition t
typeAnalysisToHTclObj (Enum t fs mwidth) =
    tag "Enum" $
        [TStr $ showType True t KStar []] ++
	-- remove the package qualifier from the enum fields
	[tagManyStr "members" (map (pvStr . unQualId) fs)] ++
	showWidth mwidth ++
	showTaggedPosition t
typeAnalysisToHTclObj (TaggedUnion t k vs isC fs mwidth) =
    tag "TaggedUnion" $
	[TStr $ showType True t k vs] ++
	showPolymorphic isC ++
        [tagLst "members" (map unionTagToHTclObj fs)] ++
	showWidth mwidth ++
	showTaggedPosition t
typeAnalysisToHTclObj (Interface t k vs isC fs pragmas) =
    -- XXX display the pragmas?
    tag "Interface" $
        [TStr $ showType True t k vs] ++
	showPolymorphic isC ++
	[tagLst "members" (map interfaceFieldToHTclObj fs)] ++
	showTaggedPosition t ++
        (if (not $ null pragmas) then  [tagLst "attributes" (map ifcPragmaToHTclObj pragmas)] else [])
typeAnalysisToHTclObj (Typeclass t k vs ps fdeps allow insts fs) =
    tag "Typeclass" $
        [TStr $ showType True t k vs] ++
        showSuperclasses ps ++
        showDependencies vs fdeps ++
        showAllowIncoherent allow ++
	[tagLst "members" (map typeclassFieldToHTclObj fs)] ++
        showInstances insts ++
	showTaggedPosition t


-----------------------------------------------------
-- Key, Name size, members fields
-- A specific display for bitify command
-- Key, Name size, members fields
-- Return structure corresponds to Tcl-level interface in SignalTypes.tcl
typeAnalysisToBitify :: TypeAnalysis -> HTclObj
--
typeAnalysisToBitify (Primary t k vs isC (Just n)) =
    tag "BASIC" [TStr $ pvStr t,
                 TStr $ show n,
                 TLst [],
                 TLst [] ]
--
typeAnalysisToBitify (Vector isC len el (Just n)) =
    tag "STRUCT" [TStr $ "Vector#(" ++ show vlen ++ ",a)",
                  TStr $ show n,
                  TLst [],
                  TLst $ map genElem [vlen-1, vlen-2..0 ] ]
    where vlen :: Int = read (pvStr len)
          elsize = fromInteger(n) `div` vlen
          genElem :: Int -> HTclObj
          genElem i = let lsb = (i) * elsize 
                      in TLst [TStr ("_[" ++ show i ++ "]"), 
                               TStr (pvStr el), 
                               TInt elsize, 
                               TInt lsb]
-- Structs
typeAnalysisToBitify (Struct t k vs isC fs (Just n)) =
    tag "STRUCT" [TStr $ showType False t k vs,
                  TStr $ show n,
                  TLst [],
                  TLst $ snd fields ]
        where genField :: (Id, Qual Type, Maybe Integer) -> (Int,[HTclObj]) ->  (Int,[HTclObj])
              genField (f,t,fw) (lsb,prev) = 
                  let err = error ("Bitify no size" ++ show f ++ ": " ++ show t) 
                      size :: Int = maybe err fromInteger fw
                  in (lsb+size,
                         TLst [TStr $ pvStr (unQualId f),
                               TStr $ pvStr t,
                               TInt size,
                               TInt lsb]:prev)
              fields :: (Int,[HTclObj])  = foldr genField (0,[]) fs
-- Tagged Unions
-- TaggedUnion Id Kind [Id] Bool [(Id, Type, Maybe Integer)] (Maybe Integer)
typeAnalysisToBitify (TaggedUnion  t k vs isC fs (Just n)) =
    tag "TAGGEDUNION"  [TStr $ showType False t k vs,
                        TStr $ show n,
                        TLst $ map genMember fs,
                        TLst $ map genField fs]
        where genMember :: (Id, Type, Maybe Integer) -> HTclObj
              genMember (i, t, mi) = TStr $ pvStr i
              --
              genField  :: (Id, Type, Maybe Integer) -> HTclObj
              genField  (i, t, mi) =
                  let err = error ("Bitify tagged union no size" ++ show i ++ ": " ++ show t) 
                  in TLst [TStr $ pvStr (unQualId i),
                                TStr $ pvStr t,
                                TInt $ maybe err fromInteger mi,
                                TInt 0]
-- Aliases
typeAnalysisToBitify (Alias t k vs atype) =
    tag "ALIAS" [TStr (pvStr atype),
                 TInt 0,
                 TLst [],
                 TLst []
                ]
typeAnalysisToBitify (Enum t fs (Just n)) =
    tag "ENUM" [TStr $ showType True t KStar [],
                TStr $ show n,
                TLst $ map (TStr . pvStr . unQualId) fs,
                TLst [] ]
-- Otherwise unknown
typeAnalysisToBitify _ =  
    tag  "UNKNOWN" [TStr "",
                    TInt 0,
                    TLst [],
                    TLst []]



typeAnalysisShort :: TypeAnalysis -> String
typeAnalysisShort (Unknown) =  "Unknown"
typeAnalysisShort (Variable) = "variable"
typeAnalysisShort (Function) = "function"
typeAnalysisShort (Numeric) = "numeric type"
typeAnalysisShort (Primary _ _ _ _ _) = ""
typeAnalysisShort (Vector _ _ _ _) = "vector"
typeAnalysisShort (List _ _) = "list"
typeAnalysisShort (Alias _ _ _ _) = "alias"
typeAnalysisShort (Struct _ _ _ _ _ _) = "struct"
typeAnalysisShort (Enum _ _ _) = "enum"
typeAnalysisShort (TaggedUnion _ _ _ _ _ _) = "tagged Union"
typeAnalysisShort (Interface _ _ _ _ _ _) = "interface"
typeAnalysisShort (Typeclass {}) = "typeclass"


-- --------------- 
-- Another variation for use with workstation.  
typeAnalysisToDetail :: TypeAnalysis -> HTclObj
typeAnalysisToDetail (Unknown) = TStr "Unknown"
typeAnalysisToDetail (Variable) = TStr "Variable"
typeAnalysisToDetail (Function) = TStr "Function"
typeAnalysisToDetail (Numeric) = TStr "Numeric Type"
typeAnalysisToDetail (Primary t k vs isC mwidth) =
    tag "Primary" $
        [TLst [TStr $ showType True t k vs]] ++
	showPolymorphic isC ++
	showWidth mwidth
typeAnalysisToDetail (Vector isC len el mwidth) =
    tag "Vector" $
        [TLst [TStr $ showType True idVector kVector vsVector]] ++
        showPolymorphic isC ++
	[tagStr "length" (pvStr len)] ++
	[tagStr "element type" (pvStr el)] ++
	showWidth mwidth
typeAnalysisToDetail (List isC el) =
    tag "List" $
        [TLst [TStr $ showType True idList kList vsList]] ++
        showPolymorphic isC ++
	[tagStr "element type" (pvStr el)]     

typeAnalysisToDetail (Alias t k vs atype) =
    tag "Alias" $
         [TLst [TStr $ showType True t k vs],
	  tagLst "Definition" [TStr (pvStr atype)]] ++
	showTaggedPosition t

typeAnalysisToDetail (Struct t k vs isC fs mwidth) =
    tag "Struct" $
        [TLst [TStr $ showType True t k vs]] ++
	showPolymorphic isC ++
	[tagLst "members" (map structFieldToDetail fs)] ++
	showWidth mwidth ++
	showTaggedPosition t

typeAnalysisToDetail (Enum t fs mwidth) =
    tag "Enum" $
        [TLst [TStr $ showType True t KStar []]] ++
	-- remove the package qualifier from the enum fields
	[tagManyStr "members" (map (pvStr . unQualId) fs)] ++
	showWidth mwidth ++
	showTaggedPosition t

typeAnalysisToDetail (TaggedUnion t k vs isC fs mwidth) =
    tag "TaggedUnion" $
	[TLst [TStr $ showType True t k vs]] ++
	showPolymorphic isC ++
        [tagLst "members" (map unionTagToDetail fs)] ++
	showWidth mwidth ++
	showTaggedPosition t

typeAnalysisToDetail  (Interface t k vs isC fs pragmas) =
    -- XXX display the pragmas?
    tag "Interface" $
        [TLst [TStr $ showType True t k vs]] ++
	showPolymorphic isC ++
	[tagLst "members" (map interfaceFieldToDetail fs)] ++
        (if (not $ null pragmas) then  [tagLst "attributes" (map ifcPragmaToHTclObj pragmas)] else []) ++
	showTaggedPosition t

typeAnalysisToDetail (Typeclass t k vs ps fdeps allow insts fs) =
    tag "Typeclass" $
        [TLst [TStr $ showType True t k vs]] ++
        showSuperclasses ps ++
        showDependencies vs fdeps ++
        showAllowIncoherent allow ++
	if (null fs) then []
                     else [tagLst "members" (map typeclassFieldToDetail fs)] ++
        showInstances insts ++
	showTaggedPosition t


-- ---------------
ifcPragmaToHTclObj :: IfcPragma -> HTclObj
ifcPragmaToHTclObj p = TStr $ "(* " ++ pvStr p ++ " *)"

commentMaybe :: PVPrint a =>  String -> Maybe a -> String
commentMaybe  _    Nothing  = ""
commentMaybe  cmt (Just i)  = intercalate " " ["//",cmt,pvStr i]

structFieldToDetail ::  (Id, Qual Type, Maybe Integer) -> HTclObj
structFieldToDetail (f, t, mi) = 
    TStr $ intercalate "  " [pvStr t,
                              pvStr (unQualId f),
                              commentMaybe "width" mi]

unionTagToDetail :: (Id, Type, Maybe Integer) -> HTclObj
unionTagToDetail (f,t, mi) =
    TStr $ intercalate "  " [pvStr t, 
                             pvStr (unQualId f),
                             commentMaybe "width" mi]

typeclassFieldToDetail ::  (Id, Qual Type) -> HTclObj
typeclassFieldToDetail (f, t) =
    TStr $ intercalate "  " [pvStr t,
                              pvStr (unQualId f)]

structFieldToHTclObj :: (Id, Qual Type, Maybe Integer) -> HTclObj
structFieldToHTclObj (f,t,n) =
    -- XXX what about the provisos?
    -- XXX what if the type is a function/module ?
    TLst $ [(TStr $ pvStr t),  (TStr $ pvStr (unQualId f))] ++ showWidth n

unionTagToHTclObj :: (Id, Type, Maybe Integer) -> HTclObj
unionTagToHTclObj (f,t, mi) =
    TLst $ [TStr (pvStr t), TStr ( pvStr (unQualId f))] ++ showWidth mi

typeclassFieldToHTclObj :: (Id, Qual Type) -> HTclObj
typeclassFieldToHTclObj (f,t) =
    -- XXX what about the provisos?
    -- XXX what if the type is a function/module ?
    TLst $ [(TStr $ pvStr t),  (TStr $ pvStr (unQualId f))]

interfaceFieldToHTclObj :: (Bool, Id, Qual Type, [IfcPragma]) -> HTclObj
interfaceFieldToHTclObj (is_subifc, fid, (ps :=> t), fpragmas) =
    if (is_subifc)
    then -- 'ps' is known to be empty
         tag "interface" [TStr (pvStr t),
                          TStr (pvStr (unQualId fid)),
                          TLst (map ifcPragmaToHTclObj fpragmas)
                         ]
    else
	let (arg_ts, res_t) = getArrows t
	in  tagLst "method" [TStr (pvStr res_t),
			     TStr (pvStr (unQualId fid)),
			     TLst (map (TStr . pvStr) arg_ts),
                             TLst (map ifcPragmaToHTclObj fpragmas)
			    ]
	    {- (if (null ps)
		then ""
		else "provisos " ++
		     inParens (commaSep (map pvStr ps))) -}


interfaceFieldToDetail :: (Bool, Id, Qual Type, [IfcPragma]) -> HTclObj
interfaceFieldToDetail (is_subifc, fid, (ps :=> t), fpragmas) =
    -- XXX display the field pragmas?
    -- XXX (could use them to give names to the args?)
    if (is_subifc)
    then -- 'ps' is known to be empty
         TStr $ intercalate "  " ["interface",
                                  pvStr t,
                                  pvpStringNQ fid]
    else
	let (arg_ts, res_t) = getArrows t
            args' = intercalate ",  " (map pvStr arg_ts)
            args = "(" ++ args' ++ ")"
        in TStr $ intercalate "  " ["method",
                                     pvStr res_t,
                                     pvpStringNQ fid,
                                     args]

showPolymorphic :: Bool -> [HTclObj]
showPolymorphic isC = if (isC) then [] else [TStr "polymorphic"]

showSuperclasses :: [Type] -> [HTclObj]
showSuperclasses ps =
    if (null ps)
    then []
    else [tagLst "superclasses" (map (TStr . pvStr) ps)]

showDependencies :: [Id] -> [[Bool]] -> [HTclObj]
showDependencies _ [bs] | not (or bs) = [] -- no dependencies
showDependencies vs fdeps =
    let sepVars (lefts, rights) [] = (lefts, rights)
        sepVars (lefts, rights) ((False, v):vs) = sepVars (v:lefts, rights) vs
        sepVars (lefts, rights) ((True, v):vs) = sepVars (lefts, v:rights) vs

        showVars [v] = pvStr v
        showVars vs = "(" ++ (intercalate ", " (map pvStr vs)) ++ ")"

        showDep bs =
            let (lefts, rights) = sepVars ([], []) (zip bs vs)
            in  TStr $ showVars (reverse lefts) ++
                       " determines " ++
                       showVars (reverse rights)
    in
        [tagLst "dependencies" (map showDep fdeps)]

showAllowIncoherent :: Maybe Bool -> [HTclObj]
showAllowIncoherent (Nothing)    = []
showAllowIncoherent (Just False) = [TStr "coherent"]
showAllowIncoherent (Just True)  = [TStr "incoherent"]

showInstances :: [Qual Type] -> [HTclObj]
showInstances insts =
    if (null insts)
    then []
    else -- for now, alphabetize the list
         let inst_strs = sort (map pvStr insts)
         in  -- XXX include position for each instance?
             [tagLst "instances" (map TStr inst_strs)]

showWidth :: Maybe Integer -> [HTclObj]
showWidth (Just w) | w <= toInteger (maxBound :: Int) = [TLst [TStr "width", TInt (fromInteger w)]]
showWidth (Just w) = [TLst [TStr "width", TStr (integerToString 10 w)]]
showWidth Nothing  = []


-- ---------------

-- String utilities

pvStr :: (PVPrint a) => a -> String
pvStr = pvpString

-- ---------------

