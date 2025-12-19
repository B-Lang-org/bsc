{-# LANGUAGE CPP #-}
module CCSyntax( CCFragment , CCType , CCExpr, CSign(..)
-- Functions for creating types
               , bitsType , classType , ptrType, doubleType
               , numType , boolType , voidType , templatedT
-- Functions for creating literal values
               , mkStr    , mkChar
               , mkBool   , mkBit
               , mkSInt8  , mkUInt8
               , mkSInt32 , mkUInt32
               , mkSInt64 , mkUInt64
               , mkFloat  , mkDouble
               , mkInitBraces
               , mkNULL
-- Functions for creating and referencing variables
               , mkVar
               , var
-- Functions for constructing typed values
               , abstract , ofType , void , bool
               , char , short , int , long
               , float , double
               , ptr , reference , array , arraySz
               , function , ctor , dtor
               , private , protected , public
               , c_struct , c_class , c_macro_class
               , userType
-- Functions for introducing signedness into types
               , unsigned , signed
-- Functions for creating declarations and specifying storage class
               , decl , construct
               , static , extern , auto , register , mutable, virtual
               , externC
-- Functions for introducing type qualifiers
               , constant , volatile
-- Functions for working with C++ namespaces
               , namespace , using , inNamespace, inNamespaceT
-- Functions for creating assignments and initializers
               , assign , assignOp
               , assignAdd , assignSub , assignMul
-- Functions for control flow
               , if_cond , switch , for
               , continue , break_loop , ret
-- Functions for joining fragments
               , joinC , block , program
-- Functions for creating function definitions
               , define , withInits
-- Functions for inserting preprocessor directives
               , cpp_if , cpp_ifdef , cpp_ifndef
               , cpp_define , cpp_define_macro
               , protect_header
               , cpp_include , cpp_system_include
-- Expression combinators
               , cDot , cArrow , cIndex , cCall
               , cPostInc , cPostDec , cPreInc , cPreDec
               , cCompl , cNot , cUMinus , cUPlus
               , cAddr , cDeref , cCast
               , cMul , cQuot, cRem
               , cAdd , cSub
               , cLShift , cRShift
               , cLt , cLe , cGt , cGe , cEq , cNe
               , cBitAnd , cBitXor , cBitOr
               , cAnd , cOr , cTernary, cComma, cGroup
-- Memory management keywords for C++
               , new , newArray
               , delete , deleteArray
-- Misc. combinators
               , stmt
               , emptyStmt
               , comment
               , literal_comment
               , blankLines
               , templated
               ) where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import Data.Maybe
import Data.List(intersperse)
import PPrint hiding ( int
                     , char
                     , float
                     , double)
import ErrorUtil(internalError)
import Util
import Numeric(showInt)
import Eval

-- import Debug.Trace

{- Notes on using the CCSyntax combinator library:

   Combinators attempt to follow C keywords as closely as possible,
   but deviate when the C syntax conflicts with a standard Haskell
   function, reserved word, or naming convention.

   The type-constructing combinators are used in English construction
   order, *NOT* in C/C++ declaration order.  This means that the
   C declarator
     char * foo;
   is created using
     ptr $ char $ (mkVar "foo")
   following the English description "pointer to character".

   The Haskell compiler will often complain if the combinators are
   used incorrectly, but not always -- the combinators allow
   construction of many syntactically invalid C/C++ programs.

   On occasion, it is necessary to convert an assignment into a
   declaration (do this using 'decl') or an expression into a
   statement (do this using 'stmt').

   Function definitions are introduced using the 'define'
   combinator to associate a function type with a function
   body.

   Preprocessor directives use a cpp_ prefix (eg., cpp_define).
-}

-- Pretty-printing shorthand
pp :: (PPrint a) => a -> Doc
pp x = pPrint PDReadable 0 x


-- Type qualifiers
data CQualifier = CTnone | CTconst | CTvolatile
  deriving (Eq, Show)

instance PPrint CQualifier where
  pPrint d p CTnone     = empty
  pPrint d p CTconst    = text "const"
  pPrint d p CTvolatile = text "volatile"

-- Sign annotations
data CSign = CTsigned | CTunsigned
  deriving (Eq, Show)

instance PPrint CSign where
  pPrint d p CTsigned   = text "signed"
  pPrint d p CTunsigned = text "unsigned"

-- Type language
data CCType = CTbool
            | CTchar
            | CTshort CSign
            | CTint CSign
            | CTlong CSign
            | CTfloat
            | CTdouble
            | CTvoid
            | CTstruct [CCFragment]
            | CTuserType String
            | CTqualified CQualifier CCType
            | CTpointer CCType
            | CTreference CCType
            | CTarray CCType (Maybe Integer)
            | CTfunction CCType [CCFragment]
            | CTconstructor [CCFragment]
            | CTdestructor
            | CTnumeric Integer
            | CTtemplate CCType [CCType]
  deriving (Eq, Show)

-- Functions for creating types

-- Get the CCType which holds (at least) a specific number of bits
bitsType :: Integer -> CSign -> CCType
bitsType n s | n ==  1                    = CTuserType "tUInt8"
             | n <=  8 && s == CTunsigned = CTuserType "tUInt8"
             | n <=  8 && s == CTsigned   = CTuserType "tSInt8"
             | n <= 32 && s == CTunsigned = CTuserType "tUInt32"
             | n <= 32 && s == CTsigned   = CTuserType "tSInt32"
             | n <= 64 && s == CTunsigned = CTuserType "tUInt64"
             | n <= 64 && s == CTsigned   = CTuserType "tSInt64"
             | n >  64 && s == CTunsigned = CTuserType "tUWide"
             | n >  64 && s == CTsigned   = CTuserType "tSWide"
             | otherwise = internalError "bitsType: invalid size or sign"

classType :: String -> CCType
classType name = CTuserType name

ptrType :: CCType -> CCType
ptrType t = CTpointer t

numType :: Integer -> CCType
numType n = CTnumeric n

boolType :: CCType
boolType = CTbool

voidType :: CCType
voidType = CTvoid

doubleType :: CCType
doubleType = CTdouble

templatedT :: CCType -> [CCType] -> CCType
templatedT t args = CTtemplate t args

-- When printing type declarations, parentheses are sometimes
-- required to distinguish, for instance, an array of pointers
-- from a pointer to an array.  These are precedence values which
-- allow pretty-printing to parenthesize correctly.
-- Higher precedence implies tighter binding.
functionPrec, arrayPrec, pointerPrec, referencePrec :: Int
functionPrec  = 3
arrayPrec     = 2
pointerPrec   = 1
referencePrec = 0

-- C type declarators are written "inside-out".  That requires
-- us to pass along partially constructed declarators, which
-- is not supported by the PPrint class.  printType takes the
-- place of a PPrint instance for CType.
printType :: CCType -> Int -> Doc -> Doc
printType CTbool _ x            = (text "bool") <+> x
printType CTchar _ x            = (text "char") <+> x
printType (CTshort s) _ x       = (pp s) <+> (text "short") <+> x
printType (CTint s) _ x         = (pp s) <+> (text "int") <+> x
printType (CTlong s) _ x        = (pp s) <+> (text "long long") <+> x
printType CTfloat _ x           = (text "float") <+> x
printType CTdouble _ x          = (text "double") <+> x
printType CTvoid _ x            = (text "void") <+> x
printType (CTstruct fields) _ x = (text "struct") <+> (pp (block fields)) <+> x
printType (CTuserType a) _ x    = (text a) <+> x
printType (CTqualified q t) p x = printType t p ((pp q) <+> x)
printType (CTpointer t) p x =
  let inner = (text "*") <> (pparen (p < pointerPrec) x)
  in printType t pointerPrec inner
printType (CTreference t) p x =
  let inner = (text "&") <> (pparen (p < referencePrec) x)
  in printType t referencePrec inner
printType (CTarray t Nothing) p x =
  let inner = (pparen (p < arrayPrec) x) <> (text "[]")
  in printType t arrayPrec inner
printType (CTarray t (Just sz)) p x =
  let inner = (pparen (p < arrayPrec) x) <>
              (text "[") <> (text (itos sz)) <> (text "]")
  in printType t arrayPrec inner
printType (CTfunction rt args) p x =
  let inner = pparen (p < functionPrec) x
      ret_type = printType rt 999 empty
      arg_list = pparen True (pp (joinC (map decl args)))
  in ret_type <+> inner <> arg_list
printType (CTconstructor args) p x =
  let inner = pparen (p < functionPrec) x
      arg_list = pparen True (pp (joinC (map decl args)))
  in inner <> arg_list
printType CTdestructor p x =
  let inner = pparen (p < functionPrec) ((text "~")<>x)
      arg_list = pparen True empty
  in inner <> arg_list
printType (CTnumeric n) _ x = (pp n) <+> x
printType (CTtemplate t args) p x =
  let arg_list = (text "<") <> commaSep (map pp args) <> (text " >")
  in (pp t) <> arg_list <+> x

instance PPrint CCType where
  pPrint d p ty = printType ty p empty

-- C storage classes
data CStorageClass  = CSnone
                    | CSstatic
                    | CSextern
                    | CSauto
                    | CSregister
                    | CSmutable
                    | CSvirtual
  deriving (Eq, Show)

instance PPrint CStorageClass where
  pPrint d p CSnone     = empty
  pPrint d p CSstatic   = text "static"
  pPrint d p CSextern   = text "extern"
  pPrint d p CSauto     = text "auto"
  pPrint d p CSregister = text "register"
  pPrint d p CSmutable  = text "mutable"
  pPrint d p CSvirtual  = text "virtual"

-- C expression term language

data CCExpr = CVar String
            | CLiteralNULL
            | CLiteralString String
            | CLiteralChar   Char
            | CLiteralBool   Bool
            | CLiteralBits1  Bool
            | CLiteralBits8  Integer CSign
            | CLiteralBits32 Integer CSign
            | CLiteralBits64 Integer CSign
            | CLiteralFloat  Float
            | CLiteralDouble Double
            | CInitBraces [CCExpr]
            | CPreOp COp CCExpr
            | CPostOp CCExpr COp
            | CBinOp CCExpr COp CCExpr
            | CGroup CCExpr
            | CFunCall CCExpr [CCExpr]
            | CArrow CCExpr String
            | CDot CCExpr String
            | CIndex CCExpr CCExpr
            | CCast CCType CCExpr
            | CDereference CCExpr
            | CAddressOf CCExpr
            | CTernary CCExpr CCExpr CCExpr
            | CNew CCType (Maybe [CCExpr]) (Maybe CCExpr)
            | CDelete CCExpr Bool
            | CTemplate CCExpr [CCType]
  deriving (Eq, Show)

-- These precedence values are used for proper grouping of non-standard
-- operators.  Other operators have their precedence encoded within COp
-- below.
dotPrec, arrowPrec, indexPrec, callPrec, addrPrec, derefPrec, castPrec, ternaryPrec :: Int
dotPrec     = 17
arrowPrec   = 17
indexPrec   = 17
callPrec    = 17
addrPrec    = 16
derefPrec   = 16
castPrec    = 16
ternaryPrec =  4

-- G++ complains about reliance on operator precedence in some expressions
-- and issues a warning suggesting to use parentheses.  To silence the warnings,
-- we use this function to define when to force use of redundant parentheses.
forceParens :: COp -> CCExpr -> Bool
forceParens op e = ((isBitOp op) && (isHigherPrec op e)) ||
                   ((isOrOp op) && (isAndExpr e))
  where isBitOp o = (o == oBitAnd) || (o == oBitOr) || (o == oBitXor) ||
                    (o == oLShift) || (o == oRShift)
        isOrOp  o = (o == oOr)
        isAndOp o = (o == oAnd)
        isHigherPrec o1 (CBinOp _ o2 _) = (prec o2) > (prec o1)
        isHigherPrec _  _               = False
        isAndExpr (CBinOp _ o _) = isAndOp o
        isAndExpr _              = False

instance PPrint CCExpr where
  pPrint d p (CVar s)                       = text s
  pPrint d p (CLiteralNULL)                 = text "NULL"
  pPrint d p (CLiteralString s)             = text (to_quoted_string s)
  pPrint d p (CLiteralChar c)               = (text "'") <> (text (show c)) <> (text "'")
  pPrint d p (CLiteralBool True)            = text "true"
  pPrint d p (CLiteralBool False)           = text "false"
  pPrint d p (CLiteralBits1 True)           = text "(tUInt8)1u"
  pPrint d p (CLiteralBits1 False)          = text "(tUInt8)0u"
  pPrint d p (CLiteralBits8 n CTunsigned)   = text ("(tUInt8)" ++ (showInt n "u"))
  pPrint d p (CLiteralBits8 n CTsigned)     = text ("(tSInt8)" ++ (show n))
  pPrint d p (CLiteralBits32 n CTunsigned)  = text (showInt n "u")
  pPrint d p (CLiteralBits32 n CTsigned)    = text (show n)
  pPrint d p (CLiteralBits64 n CTunsigned)  = text (showInt n "llu")
  pPrint d p (CLiteralBits64 n CTsigned)    = text (showInt n "ll")
  pPrint d p (CLiteralFloat x)              = text (show x)
  pPrint d p (CLiteralDouble x)             = text (show x)
  pPrint d p (CInitBraces es) =
    let val_list = commaSep (map pp es)
    in (text "{") <+> val_list <+> (text "}")
  pPrint d p (CPreOp o e)         =
    pparen (p >= prec o) ((pPrint d 0 o) <> (pPrint d (prec o) e))
  pPrint d p (CPostOp e o)        =
    pparen (p >= prec o) ((pPrint d (prec o) e) <> (pPrint d 0 o))
  pPrint d p (CBinOp e1 o e2)     =
    let -- G++ warns about relying on operator precedence for some expressions, so we put in
        -- unnecessary parentheses to make it happy.
        loperand = pparen (forceParens o e1) $ pPrint d (lprec o) e1
        op       = pPrint d 0 o
        roperand = pparen (forceParens o e2) $ pPrint d (rprec o) e2
    in pparen (p >= prec o) (hsep [loperand, op, roperand])
  pPrint d p (CGroup e)           = pparen True (pPrint d 0 e)
  pPrint d p (CFunCall fn args)   =
    let fn_name = pPrint d callPrec fn
        arg_list = commaSep (map pp args)
    in fn_name <> (pparen True (arg_list))
  pPrint d p (CArrow struct field) =
    let base = pPrint d arrowPrec struct
    in pparen (p >= arrowPrec) (base <> (text "->") <> (text field))
  pPrint d p (CDot struct field)  =
    let base = pPrint d dotPrec struct
    in -- do not parenthesize if equal precedence (left-associative anyway)
       pparen (p > dotPrec) (base <> (text ".") <> (text field))
  pPrint d p (CIndex arr idx)     =
    let array = pPrint d indexPrec arr
        index = pp idx
    in pparen (p >= indexPrec) (array <> (text "[") <> index <> (text "]"))
  pPrint d p (CCast ty e)         =
    let typ  = printType ty 999 empty
        expr = pparen True (pPrint d 0 e)
    in pparen (p >= castPrec) ((text "(") <> typ <> (text ")") <> expr)
  pPrint d p (CDereference e)     =
    pparen (p >= derefPrec) ((text "*") <> (pPrint d derefPrec e))
  pPrint d p (CAddressOf e)     =
    pparen (p >= addrPrec) ((text "&") <> (pPrint d addrPrec e))
  pPrint d p (CTernary c te fe) =
    let cdoc = pPrint d ternaryPrec c
        tdoc = pPrint d ternaryPrec te
        fdoc = pPrint d ternaryPrec fe
    in pparen (p >= ternaryPrec)
              (cdoc <+> (text "?") <+> tdoc <+> (text ":") <+> fdoc)
  pPrint d p (CNew ty Nothing Nothing) =
    (text "new") <+> (printType ty 999 empty)
  pPrint d p (CNew ty Nothing (Just e)) =
    let arr_sz = (text "[") <> (pPrint d 0 e) <> (text "]")
    in (text "new") <+> (printType ty 999 empty) <> arr_sz
  pPrint d p (CNew ty (Just args) Nothing) =
    let arg_doc = pparen True (commaSep (map pp args))
    in (text "new") <+> (printType ty 999 empty) <> arg_doc
  pPrint d p (CNew ty (Just args) (Just e)) =
    internalError "newArray with constructor arguments is not allowed"
  pPrint d p (CDelete f False) = (text "delete") <+> (pPrint d 0 f)
  pPrint d p (CDelete f True)  = (text "delete[]") <+> (pPrint d 0 f)
  pPrint d p (CTemplate e args) =
    let arg_doc = (text "<") <> commaSep (map pp args) <> (text " >")
    in pPrint d 0 e <> arg_doc

-- Operators are described by COps which contain precedence
-- and associativity information.  Higher precedence implies
-- tigher binding.  Associativity is indicated by a
-- directional precedence bias.

data COp = COp Int Int Int String
  deriving (Eq, Show)

instance PPrint COp where
  pPrint d p (COp _ _ _ s) = text s

prec :: COp -> Int
prec  (COp _ p _ _) = p
lprec :: COp -> Int
lprec (COp l _ _ _) = l
rprec :: COp -> Int
rprec (COp _ _ r _) = r

-- MUST leave 1 number between each precedence level
-- to allow room for the associativity biasing.
unaryrOp :: Int -> String -> COp
unaryrOp p s = COp 0       (2*p) (2*p)   s
infixlOp :: Int -> String -> COp
infixlOp p s = COp (2*p+1) (2*p) (2*p)   s
--unarylOp p s = COp (2*p)   (2*p) 0       s
--infixrOp p s = COp (2*p)   (2*p) (2*p+1) s

-- operator table arranged into descending precedence groups

oPostInc, oPostDec :: COp
oPostInc = unaryrOp 17 "++"
oPostDec = unaryrOp 17 "--"

oPreInc, oPreDec, oCompl, oNot, oUMinus, oUPlus :: COp
oPreInc  = unaryrOp 16 "++"
oPreDec  = unaryrOp 16 "--"
oCompl   = unaryrOp 16 "~"
oNot     = unaryrOp 16 "!"
oUMinus  = unaryrOp 16 "-"
oUPlus   = unaryrOp 16 "+"
--oCast    = unaryrOp 16 "()"

oMul, oQuot, oRem :: COp
oMul     = infixlOp 14 "*"
oQuot    = infixlOp 14 "/"
oRem     = infixlOp 14 "%"

oAdd, oSub :: COp
oAdd     = infixlOp 13 "+"
oSub     = infixlOp 13 "-"

oLShift, oRShift :: COp
oLShift  = infixlOp 12 "<<"
oRShift  = infixlOp 12 ">>"

oLt, oLe, oGt, oGe :: COp
oLt      = infixlOp 11 "<"
oLe      = infixlOp 11 "<="
oGt      = infixlOp 11 ">"
oGe      = infixlOp 11 ">="

oEq, oNe :: COp
oEq      = infixlOp 10 "=="
oNe      = infixlOp 10 "!="

oBitAnd :: COp
oBitAnd  = infixlOp  9 "&"

oBitXor :: COp
oBitXor  = infixlOp  8 "^"

oBitOr :: COp
oBitOr   = infixlOp  7 "|"

oAnd :: COp
oAnd     = infixlOp  6 "&&"

oOr :: COp
oOr      = infixlOp  5 "||"

oComma :: COp
oComma   = infixlOp  1 ","

-- C language fragments

-- Many language fragments are combined into a single structure here
-- rather than attempting to represent the byzantine structure of the
-- C/C++ language grammar.  Constraints on the structure are encoded
-- into the combinators which are used to construct CCFragments,
-- resulting in a simpler, more flexible system for building C
-- programs.

data CAccess = CApublic | CAprotected | CAprivate
  deriving (Eq, Show)

instance PPrint CAccess where
  pPrint d p CApublic    = text "public"
  pPrint d p CAprotected = text "protected"
  pPrint d p CAprivate   = text "private"

data CCFragment = CAbstract
                | CNop
                | CExpr CCExpr
                | CTyped CCType CCFragment
                | CConstruct CCFragment [CCExpr]
                | CDecl CStorageClass CCFragment
                | CAssign CCFragment CCExpr
                | CAssignOp CCFragment COp CCExpr
                | CJoin [CCFragment]
                | CBlock [CCFragment]
                | CExternBlock [CCFragment]
                | CFunctionDef CCFragment [CCExpr] CCFragment
                | CLiteralComment [String]
                | CCommented CCFragment (Maybe String)
                | CBlankLines Int
                | CProgram [CCFragment]
                | CPPIf String [CCFragment] [CCFragment]
                | CPPIfdef String [CCFragment] [CCFragment]
                | CPPIfndef String [CCFragment] [CCFragment]
                | CPPDefine String [String] (Maybe String)
                | CPPUndef String
                | CPPInclude String Bool
                | CIf CCExpr CCFragment (Maybe CCFragment)
                | CSwitch CCExpr [(CCExpr, [CCFragment])] (Maybe [CCFragment])
                | CFor CCFragment CCExpr CCFragment CCFragment
                | CContinue
                | CBreak
                | CReturn (Maybe CCExpr)
                | CSection CAccess [CCFragment]
                | CClass String (Maybe String) [CCFragment]
                | CNameSpace String [CCFragment]
                | CUsing String
  deriving (Eq, Show)

-- Print a fragment as a statement (adds a semicolon where appropriate)
printStmt :: CCFragment -> Doc
printStmt stmt@(CNop)             = semi
printStmt stmt@(CDecl _ _)        = (pp stmt) <> semi
printStmt stmt@(CConstruct _ _)   = (pp stmt) <> semi
printStmt stmt@(CAssign _ _)      = (pp stmt) <> semi
printStmt stmt@(CAssignOp _ _ _)  = (pp stmt) <> semi
printStmt stmt@(CExpr _)          = (pp stmt) <> semi
printStmt stmt@(CContinue)        = (pp stmt) <> semi
printStmt stmt@(CBreak)           = (pp stmt) <> semi
printStmt stmt@(CReturn _)        = (pp stmt) <> semi
printStmt stmt@(CClass _ _ _)     = (pp stmt) <> semi
printStmt stmt@(CUsing _)         = (pp stmt) <> semi
printStmt (CLiteralComment ls)    = (text "") $+$ (ppComment ls)
printStmt (CCommented x Nothing)  = printStmt x
printStmt (CCommented x (Just s)) =
  (text "") $+$ (ppWrappedComment s) $+$ (printStmt x)
printStmt stmt                    = pp stmt

-- If it's a block, print it as is, otherwise indent it first
printClauseOrBlock :: CCFragment -> Doc
printClauseOrBlock blk@(CBlock _) = pp blk
printClauseOrBlock clause         = nest 2 (printStmt clause)

-- Print a comment, with text wrapping
ppWrappedComment :: String -> Doc
ppWrappedComment s = ppComment (wrap (lines s))

-- Print a comment, without wrapping the text
ppComment :: [String] -> Doc
ppComment []     = text "/* */"
ppComment (l:ls) = let first_line = (text "/*") <+> (text l)
                       body = map (\x->(text " *") <+> (text x)) ls
                   in case body of
                        [] -> first_line <+> (text "*/")
                        _  -> vsep ([first_line] ++ body ++ [text " */"])

-- Print a fragment
instance PPrint CCFragment where
  pPrint d p CAbstract               = empty
  pPrint d p CNop                    = empty
  pPrint d p (CExpr e)               = pPrint d p e
  pPrint d p (CTyped t f)            = pPrint d 0 f
  pPrint d p x@(CDecl sc (CTyped t (CAssign lhs rhs))) =
    (pPrint d 0 sc) <+> (printType t 999 (pPrint d 0 lhs)) <+>
    (text "=") <+> (pPrint d 0 rhs)
  pPrint d p (CDecl sc (CTyped t f)) =
    (pPrint d 0 sc) <+> (printType t 999 (pPrint d 0 f))
  pPrint d p (CDecl sc (CJoin fs))   =
    (pPrint d 0 sc) <+> (pPrint d 0 (CJoin (map decl fs)))
  pPrint d p (CDecl sc f)            = (pPrint d 0 sc) <+> (pPrint d 0 f)
  pPrint d p (CConstruct (CTyped t f) []) =
    (printType t 999 (pPrint d 0 f))
  pPrint d p (CConstruct (CTyped t f) ps) =
    (printType t 999 (pPrint d 0 f)) <>
    (pparen True (commaSep (map pp ps)))
  pPrint d p (CAssign lhs rhs)       =
    let l = pPrint d 0 lhs
        r = pPrint d 0 rhs
    in l <+> (text "=") <+> r
  pPrint d p (CAssignOp lhs op rhs)  =
    let l = pPrint d 0 lhs
        r = pPrint d 0 rhs
    in l <+> (pp op) <> (text "=") <+> r
  pPrint d p (CJoin fs)              =
    commaSep [pPrint d (prec oComma) x | x <- fs]
  pPrint d p (CBlock fs)             =
    let body = vsep (map printStmt fs)
    in (text "{") $+$ (nest 2 body) $+$ (text "}")
  pPrint d p (CExternBlock fs)             =
    let body = vsep (map printStmt fs)
    in (text "extern \"C\" {") $+$ (nest 2 body) $+$ (text "}")
  pPrint d p (CFunctionDef prt@(CDecl _ _) [] body@(CBlock _)) =
    pp prt $+$ pp body
  pPrint d p (CFunctionDef prt@(CDecl _ _) initlist body@(CBlock _)) =
    let ilist = commaSep [pPrint d (prec oComma) x | x <- initlist]
    in pp prt $+$ (nest 2 ((text ":") <+> ilist)) $+$ pp body
  pPrint d p (CFunctionDef prt@(CDecl _ _) initlist body) =
    pp (CFunctionDef prt initlist (CBlock [body]))
  pPrint d p (CFunctionDef prt initlist body) =
    pp (CFunctionDef (decl prt) initlist body)
  pPrint d p (CLiteralComment ls)    = (text "") $+$ (ppComment ls)
  pPrint d p (CCommented x Nothing)  = pPrint d p x
  pPrint d p (CCommented x (Just s)) =
    (text "") $+$ (ppWrappedComment s) $+$ (pPrint d p x)
  pPrint d p (CBlankLines n)         = vsep (take n (repeat (text "")))
  pPrint d p (CProgram fs)           = vsep (map printStmt fs)
  pPrint d p (CPPIf c ts es)         =
    let cond  = text ("#if " ++ c)
        thens = vsep (map printStmt ts)
        elses = if (null es)
                then empty
                else text ("#else  /* if " ++ c ++ " */") $+$
                     vsep (map printStmt es)
        end   = text ("#endif /* if " ++ c ++ " */")
    in cond $+$ thens $+$ elses $+$ end
  pPrint d p (CPPIfdef c ts es)      =
    let cond  = text ("#ifdef " ++ c)
        thens = vsep (map printStmt ts)
        elses = if (null es)
                then empty
                else text ("#else  /* ifdef " ++ c ++ " */") $+$
                     vsep (map printStmt es)
        end   = text ("#endif /* ifdef " ++ c ++ " */")
    in cond $+$ thens $+$ elses $+$ end
  pPrint d p (CPPIfndef c ts es)     =
    let cond  = text ("#ifndef " ++ c)
        thens = vsep (map printStmt ts)
        elses = if (null es)
                then empty
                else text ("#else  /* ifndef " ++ c ++ " */") $+$
                     vsep (map printStmt es)
        end   = text ("#endif /* ifndef " ++ c ++ " */")
    in cond $+$ thens $+$ elses $+$ end
  pPrint d p (CPPDefine n args b)    =
    let def = text ("#define " ++ n)
        arg_list = if (null args)
                   then empty
                   else pparen True (hsep (intersperse comma (map text args)))
        body = case b of
                 (Just s) -> text s
                 Nothing  -> empty
    in def <> arg_list <+> body
  pPrint d p (CPPUndef n)            = text ("#undef " ++ n)
  pPrint d p (CPPInclude file True)  = text ("#include <" ++ file ++ ">")
  pPrint d p (CPPInclude file False) = text ("#include \"" ++ file ++ "\"")
  pPrint d p (CIf c th Nothing)      =
    -- If the true-arm is a nested if-stmt with an else-clause,
    -- possibly under layers of for-stmts with single elements,
    -- then braces are needed to avoid an ambiguous-else warning
    let needsBraces (CIf _ _ (Just _)) = True
        needsBraces (CFor _ _ _ b) = needsBraces b
        needsBraces _ = False
        th' = if (needsBraces th) then CBlock [th] else th
    in  (text "if (") <> (pp c) <> (text ")") $+$ (printClauseOrBlock th')
  pPrint d p (CIf c th (Just el))    =
    -- If the true-arm is a nested if-stmt without an else-clause,
    -- possibly under layers of for-stmts with single elements,
    -- then braces are needed for correct parsing
    let needsBraces (CIf _ _ Nothing) = True
        needsBraces (CFor _ _ _ b) = needsBraces b
        needsBraces _ = False
        th' = if (needsBraces th) then CBlock [th] else th
    in  (text "if (") <> (pp c) <> (text ")") $+$
        (printClauseOrBlock th') $+$ (text "else") $+$ (printClauseOrBlock el)
  pPrint d p (CSwitch idx arms deflt) =
    let ppArm (n, blk) = (text "case") <+> (pp n) <> (text ":") $+$
                         nest 2 (vsep (map printStmt blk))
        ppDefault (Just blk) = (text "default:") $+$
                               nest 2 (vsep (map printStmt blk))
        ppDefault (Nothing)  = empty
    in (text "switch (") <> (pp idx) <> (text ") {") $+$
       vsep (map ppArm arms) $+$
       ppDefault deflt $+$
       (text "}")
  pPrint d p (CFor init test advance body) =
    let header = (text "for (") <> (pp init) <> semi <+>
                                   (pp test) <> semi <+>
                                   (pp advance) <> (text ")")
    in header $+$ (printClauseOrBlock body)
  pPrint d p CContinue               = text "continue"
  pPrint d p CBreak                  = text "break"
  pPrint d p (CReturn Nothing)       = text "return"
  pPrint d p (CReturn (Just expr))   = (text "return") <+> (pp expr)
  pPrint d p (CSection acc fs)  =
    let body = vsep (map printStmt fs)
    in (pp acc) <> colon $+$ (nest 1 body)
  pPrint d p (CClass name Nothing sections)  =
    let body = vsep (map pp sections)
    in (text name) <+> (text "{") $$
       (nest 1 body) $$
       (text "}")
  pPrint d p (CClass name (Just super) sections)  =
    let body = vsep (map pp sections)
    in (text name) <+> (text (": public " ++ super)) <+> (text "{") $$
       (nest 1 body) $$
       (text "}")
  pPrint d p (CNameSpace name fs) =
    let body = vsep (map printStmt fs)
    in (text "namespace") <+> (text name) $+$
       (text "{") $+$
       (nest 2 body) $+$
       (text "}")
  pPrint d p (CUsing name) = (text "using namespace") <+> (text name)
  pPrint d p f = internalError ("malformed CCFragment reached pPrint: " ++
                                (show f))

-----------------
-- Combinator library for building CCFragments

-- Functions for creating literals

mkStr :: String -> CCExpr
mkStr s = CLiteralString s

mkChar :: Char -> CCExpr
mkChar c = CLiteralChar c

mkBool :: Bool -> CCExpr
mkBool b = CLiteralBool b

mkBit :: Integer -> CCExpr
mkBit 0 = CLiteralBits1 False
mkBit _ = CLiteralBits1 True

mkSInt8 :: Integer -> CCExpr
mkSInt8 n = CLiteralBits8 n CTsigned

mkUInt8 :: Integer -> CCExpr
mkUInt8 n = CLiteralBits8 n CTunsigned

mkSInt32 :: Integer -> CCExpr
mkSInt32 n = CLiteralBits32 n CTsigned

mkUInt32 :: Integer -> CCExpr
mkUInt32 n = CLiteralBits32 n CTunsigned

mkSInt64 :: Integer -> CCExpr
mkSInt64 n = CLiteralBits64 n CTsigned

mkUInt64 :: Integer -> CCExpr
mkUInt64 n = CLiteralBits64 n CTunsigned

mkFloat :: Float -> CCExpr
mkFloat x = CLiteralFloat x

mkDouble :: Double -> CCExpr
mkDouble x = CLiteralDouble x

mkInitBraces :: [CCExpr] -> CCExpr
mkInitBraces es = CInitBraces es

mkNULL :: CCExpr
mkNULL = CLiteralNULL

-- Functions for creating and referencing variables

mkVar :: String -> CCFragment
mkVar name = CExpr (var name)

var :: String -> CCExpr
var name = CVar name

-- Functions for constructing types and adding types to values

abstract :: CCFragment  -- used when constructing pure types
abstract = CAbstract

-- add a type to a value
ofType :: CCFragment -> CCType -> CCFragment
ofType v ty = CTyped ty v

void :: CCFragment -> CCFragment
void v = v `ofType` CTvoid

bool :: CCFragment -> CCFragment
bool v = v `ofType` CTbool

char :: CCFragment -> CCFragment
char v = v `ofType` CTchar

short :: CCFragment -> CCFragment
short v = v `ofType` (CTshort CTsigned)

int :: CCFragment -> CCFragment
int v = v `ofType` (CTint CTsigned)

long :: CCFragment -> CCFragment
long v = v `ofType` (CTlong CTsigned)

float :: CCFragment -> CCFragment
float v = v `ofType` CTfloat

double :: CCFragment -> CCFragment
double v = v `ofType` CTdouble

ptr :: CCFragment -> CCFragment
ptr (CTyped t v) = v `ofType` (CTpointer t)
ptr _ = internalError "ptr applies only to typed vars"

reference :: CCFragment -> CCFragment
reference (CTyped t v) = v `ofType` (CTreference t)
reference _ = internalError "reference applies only to typed vars"

array :: CCFragment -> CCFragment
array (CTyped t v) = v `ofType` (CTarray t Nothing)
array _ = internalError "array applies only to typed vars"

arraySz :: Integer -> CCFragment -> CCFragment
arraySz sz (CTyped t v) = v `ofType` (CTarray t (Just sz))
arraySz _ _ = internalError "arraySz applies only to typed vars"

c_struct :: [CCFragment] -> CCFragment -> CCFragment
c_struct sections v = v `ofType` (CTstruct sections)

userType :: String -> CCFragment -> CCFragment
userType name v = v `ofType` (CTuserType name)

function :: (CCFragment -> CCFragment) -> CCFragment -> [CCFragment]
         -> CCFragment
function retC v args =
  case (retC CAbstract) of
    (CTyped retT _) -> v `ofType` (CTfunction retT args)
    _ -> internalError "CCSyntax function"

ctor :: CCFragment -> [CCFragment] -> CCFragment
ctor v args = v `ofType` (CTconstructor args)

dtor :: CCFragment -> CCFragment
dtor v = v `ofType` CTdestructor

private :: [CCFragment] -> CCFragment
private fs = CSection CAprivate fs

protected :: [CCFragment] -> CCFragment
protected fs = CSection CAprotected fs

public :: [CCFragment] -> CCFragment
public fs = CSection CApublic fs

c_class :: String -> Maybe String -> [CCFragment] -> CCFragment
c_class name superclass sections = CClass ("class " ++ name) superclass sections

c_macro_class :: String -> Maybe String -> [CCFragment] -> CCFragment
c_macro_class name superclass sections = CClass name superclass sections

-- Functions for introducing signedness into types

unsigned :: CCFragment -> CCFragment
unsigned (CTyped CTchar v)      =
    internalError "characters do not support sign annotations"
unsigned (CTyped (CTshort _) v) = (CTyped (CTshort CTunsigned) v)
unsigned (CTyped (CTint _)   v) = (CTyped (CTint   CTunsigned) v)
unsigned (CTyped (CTlong _)  v) = (CTyped (CTlong  CTunsigned) v)
unsigned v                      = (CTyped (CTint   CTunsigned) v)

signed :: CCFragment -> CCFragment
signed (CTyped CTchar v)      =
    internalError "characters do not support sign annotations"
signed (CTyped (CTshort _) v) = (CTyped (CTshort CTsigned) v)
signed (CTyped (CTint _)   v) = (CTyped (CTint   CTsigned) v)
signed (CTyped (CTlong _)  v) = (CTyped (CTlong  CTsigned) v)
signed v                      = (CTyped (CTint   CTsigned) v)

-- Functions for creating declarations and specifying storage class

decl :: CCFragment -> CCFragment
decl v = CDecl CSnone v

construct :: CCFragment -> [CCExpr] -> CCFragment
construct v ps = decl (CConstruct v ps)

static :: CCFragment -> CCFragment
static v = CDecl CSstatic v

extern :: CCFragment -> CCFragment
extern v = CDecl CSextern v

auto :: CCFragment -> CCFragment
auto v = CDecl CSauto v

register :: CCFragment -> CCFragment
register v = CDecl CSregister v

mutable :: CCFragment -> CCFragment
mutable v = CDecl CSmutable v

virtual :: CCFragment -> CCFragment
virtual v = CDecl CSvirtual v

externC :: [CCFragment] -> CCFragment
externC fs = CExternBlock fs

-- Functions for introducing type qualifiers

constant :: CCFragment -> CCFragment
constant (CTyped t v) = CTyped (CTqualified CTconst t) v
constant _            = internalError "constant applies only to typed vars"

volatile :: CCFragment -> CCFragment
volatile (CTyped t v) = CTyped (CTqualified CTvolatile t) v
volatile _            = internalError "volatile applies only to typed vars"

-- Functions for working with C++ namespaces

namespace :: String -> [CCFragment] -> CCFragment
namespace name fs = CNameSpace name fs

using :: String -> CCFragment
using name = CUsing name

inNamespace :: CCExpr -> String -> CCExpr
inNamespace (CVar var) name = CVar (name ++ "::" ++ var)
inNamespace e          _    = e

inNamespaceT :: CCType -> String -> CCType
inNamespaceT (CTuserType t)    name = CTuserType (name ++ "::" ++ t)
inNamespaceT (CTqualified q t) name = CTqualified q (t `inNamespaceT` name)
inNamespaceT (CTpointer t)     name = CTpointer (t `inNamespaceT` name)
inNamespaceT (CTreference t)   name = CTreference (t `inNamespaceT` name)
inNamespaceT (CTarray t s)     name = CTarray (t `inNamespaceT` name) s
inNamespaceT (CTfunction t b)  name = CTfunction (t `inNamespaceT` name) b
inNamespaceT t                 _    = t

-- Functions for creating assignments and initializers

assign :: CCFragment -> CCExpr -> CCFragment
assign lhs rhs = CAssign lhs rhs

assignOp :: CCFragment -> COp -> CCExpr -> CCFragment
assignOp lhs op rhs = CAssignOp lhs op rhs

assignAdd :: CCFragment -> CCExpr -> CCFragment
assignAdd lhs rhs = assignOp lhs oAdd rhs

assignSub :: CCFragment -> CCExpr -> CCFragment
assignSub lhs rhs = assignOp lhs oSub rhs

assignMul :: CCFragment -> CCExpr -> CCFragment
assignMul lhs rhs = assignOp lhs oMul rhs

-- Functions for control flow

if_cond :: CCExpr -> CCFragment -> (Maybe CCFragment) -> CCFragment
if_cond c th el =
  case c of
    (CLiteralBool True)   -> case th of
                               (CBlock []) -> emptyStmt
                               otherwise   -> th
    (CLiteralBits1 True)  -> case th of
                               (CBlock []) -> emptyStmt
                               otherwise   -> th
    (CLiteralBool False)  -> if (isJust el)
                             then fromJust el
                             else comment "dead code removed here" emptyStmt
    (CLiteralBits1 False) -> if (isJust el)
                             then fromJust el
                             else comment "dead code removed here" emptyStmt
    otherwise             -> CIf c th el

switch :: CCExpr -> [(CCExpr, [CCFragment])] -> Maybe [CCFragment] ->
          CCFragment
switch idx arms deflt = CSwitch idx arms deflt

for :: CCFragment -> CCExpr -> CCFragment -> CCFragment -> CCFragment
for init test advance body = CFor init test advance body

continue :: CCFragment
continue = CContinue

break_loop :: CCFragment
break_loop = CBreak

ret :: Maybe CCExpr -> CCFragment
ret = CReturn

-- Function for joining fragments

joinC :: [CCFragment] -> CCFragment
joinC fs = CJoin fs

block :: [CCFragment] -> CCFragment
block fs = CBlock fs

program :: [CCFragment] -> CCFragment
program fs = CProgram fs

-- Function for creating function definitions

define :: CCFragment -> CCFragment -> CCFragment
define prt@(CTyped (CTfunction _ _) _)  body = CFunctionDef prt [] body
define prt@(CTyped (CTconstructor _) _) body = CFunctionDef prt [] body
define prt@(CTyped CTdestructor _)      body = CFunctionDef prt [] body
define _ _ = internalError "define applies only to functions, ctors & dtors"

-- Function for specifying an initializer list for a constructor function.
-- The CCExprs should be calls to constructor functions.
withInits :: CCFragment -> [CCExpr] -> CCFragment
withInits (CFunctionDef prt initlist body) add_inits =
  CFunctionDef prt (initlist ++ add_inits) body
withInits _ _ = internalError "withInits applies only to constructor defs"

-- Functions for inserting preprocessor directives

cpp_if :: String -> [CCFragment] -> [CCFragment] -> CCFragment
cpp_if s ts es = CPPIf s ts es

cpp_ifdef :: String -> [CCFragment] -> [CCFragment] -> CCFragment
cpp_ifdef s ts es = CPPIfdef s ts es

cpp_ifndef :: String -> [CCFragment] -> [CCFragment] -> CCFragment
cpp_ifndef s ts es = CPPIfndef s ts es

cpp_define :: String -> Maybe String -> CCFragment
cpp_define s v = CPPDefine s [] v

cpp_define_macro :: String -> [String] -> Maybe String -> CCFragment
cpp_define_macro s args v = CPPDefine s args v

protect_header :: String -> [CCFragment] -> CCFragment
protect_header name body =
  let dstr = "__" ++ name ++ "_h__"
      def  = cpp_define dstr Nothing
  in cpp_ifndef dstr ([def, blankLines 1] ++ body ++ [blankLines 1]) []

cpp_include :: String -> CCFragment
cpp_include filename = CPPInclude filename False

cpp_system_include :: String -> CCFragment
cpp_system_include filename = CPPInclude filename True

-- Utility functions for working with constants

isLiteral :: CCExpr -> Bool
isLiteral (CLiteralBool _)     = True
isLiteral (CLiteralBits1 _)    = True
isLiteral (CLiteralBits8 _ _)  = True
isLiteral (CLiteralBits32 _ _) = True
isLiteral (CLiteralBits64 _ _) = True
isLiteral _                    = False

isZero :: CCExpr -> Bool
isZero (CLiteralBits1 False) = True
isZero (CLiteralBits8  0 _)  = True
isZero (CLiteralBits32 0 _)  = True
isZero (CLiteralBits64 0 _)  = True
isZero _                     = False

isFalse :: CCExpr -> Bool
isFalse (CLiteralBool False) = True
isFalse x                    = isZero x

isTrue :: CCExpr -> Bool
isTrue (CLiteralBool True) = True
isTrue x | isLiteral x     = not (isZero x)
isTrue _                   = False

-- Combinators for C operators

binOp :: COp -> CCExpr -> CCExpr -> CCExpr
binOp  op x y = CBinOp x op y
preOp :: COp -> CCExpr -> CCExpr
preOp  op x   = CPreOp op x
postOp :: COp -> CCExpr -> CCExpr
postOp op x   = CPostOp x op

cPostInc, cPostDec, cPreInc, cPreDec :: CCExpr -> CCExpr
cPostInc = postOp oPostInc
cPostDec = postOp oPostDec
cPreInc  = preOp oPreInc
cPreDec  = preOp oPreDec

cCompl, cNot, cUMinus, cUPlus :: CCExpr -> CCExpr
cCompl   = preOp oCompl
cNot     = preOp oNot
cUMinus  = preOp oUMinus
cUPlus   = preOp oUPlus

cMul, cQuot, cRem, cAdd, cSub, cLShift, cRShift :: CCExpr -> CCExpr -> CCExpr
cMul     = binOp oMul
cQuot    = binOp oQuot
cRem     = binOp oRem
cAdd     = binOp oAdd
cSub     = binOp oSub
cLShift x y | isZero x || isZero y = x
            | otherwise = binOp oLShift x y
cRShift x y | isZero x || isZero y = x
            | otherwise = binOp oRShift x y

cLt, cLe, cGt, cGe, cEq, cNe :: CCExpr -> CCExpr -> CCExpr
cLt      = binOp oLt
cLe      = binOp oLe
cGt      = binOp oGt
cGe      = binOp oGe
cEq      = binOp oEq
cNe      = binOp oNe

cBitAnd, cBitXor, cBitOr, cAnd, cOr, cComma :: CCExpr -> CCExpr -> CCExpr
cBitAnd  = binOp oBitAnd
cBitXor  = binOp oBitXor
cBitOr x y | isZero x = y
           | isZero y = x
           | otherwise = binOp oBitOr x y
cAnd x y | isFalse x || isFalse y = mkBool False
         | isTrue x = y
         | isTrue y = x
         | otherwise = binOp oAnd x y
cOr x y | isTrue x || isTrue y = mkBool True
        | isFalse x = y
        | isFalse y = x
        | otherwise = binOp oOr x y
cComma   = binOp oComma

cDot :: CCExpr -> String -> CCExpr
cDot struct field = struct `CDot` field

cArrow :: CCExpr -> String -> CCExpr
cArrow struct_ptr field = struct_ptr `CArrow` field

cIndex :: CCExpr -> CCExpr -> CCExpr
cIndex arr idx  = arr `CIndex` idx

cCall :: CCExpr -> [CCExpr] -> CCExpr
cCall fn args = fn `CFunCall` args

cAddr :: CCExpr -> CCExpr
cAddr val = CAddressOf val

cDeref :: CCExpr -> CCExpr
cDeref ptr = CDereference ptr

cCast :: CCType -> CCExpr -> CCExpr
cCast typ expr = typ `CCast` expr

cTernary :: CCExpr -> CCExpr -> CCExpr -> CCExpr
cTernary cond true_expr false_expr = CTernary cond true_expr false_expr

cGroup :: CCExpr -> CCExpr
cGroup expr = CGroup expr

-- Memory management keywords for C++
new :: CCType -> (Maybe [CCExpr]) -> CCExpr
new ty args = CNew ty args Nothing

newArray :: CCType -> CCExpr -> CCExpr
newArray ty e = CNew ty Nothing (Just e)

delete :: CCExpr -> CCExpr
delete e = CDelete e False

deleteArray :: CCExpr -> CCExpr
deleteArray e = CDelete e True

-- Function for turning an expression into a statement

stmt :: CCExpr -> CCFragment
stmt expr = CExpr expr

emptyStmt :: CCFragment
emptyStmt = CNop

-- Functions for inserting comments

-- comment text may be wrapped
comment :: String -> CCFragment -> CCFragment
comment txt v = CCommented v (Just txt)

-- comment text will not be wrapped
-- (for when layout of comment text is significant)
literal_comment :: [String] -> CCFragment
literal_comment ls = CLiteralComment ls

-- Function for introducing whitespace for readability

blankLines :: Int -> CCFragment
blankLines n = CBlankLines n


templated :: CCExpr -> [CCType] -> CCExpr
templated e args = CTemplate e args

-- ----------
-- Hyper instance needed for dumping CCFragments

instance NFData CCFragment where
  rnf CAbstract = ()
  rnf CNop = ()
  rnf (CExpr e) = rnf e
  rnf (CTyped t f) = rnf2 t f
  rnf (CConstruct f es) = rnf2 f es
  rnf (CDecl sc f) = rnf2 sc f
  rnf (CAssign f e) = rnf2 f e
  rnf (CAssignOp f op e) = rnf3 f op e
  rnf (CJoin fs) = rnf fs
  rnf (CBlock fs) = rnf fs
  rnf (CExternBlock fs) = rnf fs
  rnf (CFunctionDef f args body) = rnf3 f args body
  rnf (CLiteralComment ss) = rnf ss
  rnf (CCommented f ms) = rnf2 f ms
  rnf (CBlankLines n) = rnf n
  rnf (CProgram fs) = rnf fs
  rnf (CPPIf c ts es) = rnf3 c ts es
  rnf (CPPIfdef c ts es) = rnf3 c ts es
  rnf (CPPIfndef c ts es) = rnf3 c ts es
  rnf (CPPDefine n args b) = rnf3 n args b
  rnf (CPPUndef s) = rnf s
  rnf (CPPInclude file b) = rnf2 file b
  rnf (CIf c thn mels) = rnf3 c thn mels
  rnf (CSwitch idx arms deflt) = rnf3 idx arms deflt
  rnf (CFor init test advance body) = rnf4 init test advance body
  rnf CContinue = ()
  rnf CBreak = ()
  rnf (CReturn me) = rnf me
  rnf (CSection acc fs) = rnf2 acc fs
  rnf (CClass name superclass sections) = rnf3 name superclass sections
  rnf (CNameSpace name fs) = rnf2 name fs
  rnf (CUsing name) = rnf name

instance NFData CCExpr where
  rnf (CVar s) = rnf s
  rnf CLiteralNULL = ()
  rnf (CLiteralString s) = rnf s
  rnf (CLiteralChar c) = rnf c
  rnf (CLiteralBool b) = rnf b
  rnf (CLiteralBits1 b) = rnf b
  rnf (CLiteralBits8 n s) = rnf2 n s
  rnf (CLiteralBits32 n s) = rnf2 n s
  rnf (CLiteralBits64 n s) = rnf2 n s
  rnf (CLiteralFloat f) = rnf f
  rnf (CLiteralDouble d) = rnf d
  rnf (CInitBraces es) = rnf es
  rnf (CPreOp op e) = rnf2 op e
  rnf (CPostOp e op) = rnf2 e op
  rnf (CBinOp e1 op e2) = rnf3 e1 op e2
  rnf (CGroup e) = rnf e
  rnf (CFunCall fn args) = rnf2 fn args
  rnf (CArrow struct field) = rnf2 struct field
  rnf (CDot struct field) = rnf2 struct field
  rnf (CIndex arr idx) = rnf2 arr idx
  rnf (CCast ty e) = rnf2 ty e
  rnf (CDereference e) = rnf e
  rnf (CAddressOf e) = rnf e
  rnf (CTernary c t f) = rnf3 c t f
  rnf (CNew t margs me) = rnf3 t margs me
  rnf (CDelete e b) = rnf2 e b
  rnf (CTemplate e args) = rnf2 e args

instance NFData CCType where
  rnf CTbool = ()
  rnf CTchar = ()
  rnf (CTshort s) = rnf s
  rnf (CTint s) = rnf s
  rnf (CTlong s) = rnf s
  rnf CTfloat = ()
  rnf CTdouble = ()
  rnf CTvoid = ()
  rnf (CTstruct fields) = rnf fields
  rnf (CTuserType name) = rnf name
  rnf (CTqualified q t) = rnf2 q t
  rnf (CTpointer t) = rnf t
  rnf (CTreference t) = rnf t
  rnf (CTarray t mn) = rnf2 t mn
  rnf (CTfunction rt args) = rnf2 rt args
  rnf (CTconstructor args) = rnf args
  rnf CTdestructor = ()
  rnf (CTnumeric n) = rnf n
  rnf (CTtemplate t args) = rnf2 t args

instance NFData CStorageClass where
  rnf CSnone = ()
  rnf CSstatic = ()
  rnf CSextern = ()
  rnf CSauto = ()
  rnf CSregister = ()
  rnf CSmutable = ()
  rnf CSvirtual = ()

instance NFData CAccess where
  rnf CApublic = ()
  rnf CAprotected = ()
  rnf CAprivate = ()

instance NFData COp where
  rnf (COp l p r s) = rnf4 l p r s

instance NFData CSign where
  rnf CTsigned = ()
  rnf CTunsigned = ()

instance NFData CQualifier where
  rnf CTnone = ()
  rnf CTconst = ()
  rnf CTvolatile = ()
