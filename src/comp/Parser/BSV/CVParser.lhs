
> {-# OPTIONS_GHC -Wall -fno-warn-unused-matches -fno-warn-name-shadowing #-}

> module Parser.BSV.CVParser {- (bsvParseString, bsvParseFile) -} where

> import Data.Char
> import Data.List(mapAccumL, group, groupBy, intercalate, sort, partition, nub)
> import Data.Maybe
> import Control.Monad
> import qualified Data.Set as S
> -- import Debug.Trace

> import Parsec hiding(getPosition)
> import qualified Parsec(getPosition)
> import ParsecExpr
> import PVPrint hiding(parens, colon, semi, comma, braces, brackets, char)
> import PPrint (ppReadable)
> import FStringCompat
> import Position
> import Id
> import CSyntax
> import CSyntaxUtil
> import qualified VModInfo as V
> import SchedInfo
> import PreStrings
> import PreIds
> import Type
> import IntLit
> import Error(internalError, EMsg, WMsg, ErrMsg(..),
>              ErrorHandle, bsError, bsWarning, exitOK)
> import Flags(Flags, DumpFlag(..),
>              stdlibNames, disableAssertions, preprocessOnly, genName)
> import Util
> import Parser.BSV.CVParserCommon
> import Parser.BSV.CVParserImperative
> import Pragma
> import SystemVerilogPreprocess(preprocess)
> import SystemVerilogScanner(scan)
> import SystemVerilogTokens
> import SystemVerilogKeywords

for preprocessor and token dumping

> import TopUtils
> import FileNameUtil

> import qualified Lex
> import qualified Parse
> import qualified Parser.Classic.CParser as CParser

keep all identifiers regardless of (* keep *)?

> isGlobalKeep :: Bool
> isGlobalKeep = True

Test whether a token is accepted given an accept function.  Turn any
encountered scanner errors into parser errors and throw up on any
comments that have survived by accident.

> pToken :: (SV_Token -> Maybe a) -> SV_Parser a
> pToken accept =
>         token svTokenToString start_position accept
>     <|> (token svTokenToString start_position acceptError >>= failWithErr)
>     where acceptError (SV_Token_Error { start_position = pos, errMessage = msg }) =
>               Just (pos, msg)
>           acceptError (SV_Token_Comment { start_position = pos }) =
>               internalError ("CVParser: Unhandled comment at " ++
>                              prPosition pos)
>           acceptError _ = Nothing

Parse a specific symbol, or emit an error that the symbol was expected

> pSymbol :: SV_Symbol -> SV_Parser ()
> pSymbol acceptedSym = pToken accept <?> expected
>     where accept (SV_Token_Symbol { symbol = sym })
>               | sym == acceptedSym = Just ()
>           accept _ = Nothing
>           expected = svTokenToString
>                      -- the token below is constructed only for the purpose
>                      -- of pretty-printing it with svTokenToString
>                      (SV_Token_Symbol { start_position = errPos,
>                                       end_position = errPos,
>                                         symbol = acceptedSym })
>           errPos = internalError
>                    "CVParser.pSymbol: svTokenToString forced position"

Parse a specific keyword, or emit an error that the keyword was expected

> pKeyword :: SV_Keyword -> SV_Parser ()
> pKeyword acceptedKeyword = pToken accept <?> expected
>     where accept (SV_Token_Keyword { keyword = kw })
>               | kw == acceptedKeyword = Just ()
>           accept _ = Nothing
>           expected = svTokenToString
>                      -- the token below is constructed only for the purpose
>                      -- of pretty-printing it with svTokenToString
>                      (SV_Token_Keyword { start_position = errPos,
>                                       end_position = errPos,
>                                          keyword = acceptedKeyword })
>           errPos = internalError
>                    "CVParser.pKeyword: svTokenToString forced position"

Parse an identifier (starting with lowercase)

> pIdentifier :: SV_Parser Id  -- i.e. an unqualified identifier
> pIdentifier = pToken accept <?> "identifier starting with lowercase"
>     where accept (SV_Token_Id { start_position = pos,
>                               end_position = errPos,
>                               name = s@(c:_) })
>               | not (isUpper c) = Just (mkId pos (mkFString s))
>           accept _ = Nothing

> pUorLIdentifier :: SV_Parser Id  -- i.e. same, but can also begin with uppercase
> pUorLIdentifier = pToken accept <?> "identifier"
>     where accept (SV_Token_Id { start_position = pos,
>                               end_position = errPos,
>                               name = s })
>               = Just (mkId pos (mkFString s))
>           accept _ = Nothing

Parse either an identifier or an n-tuple of identifiers, e.g., "{ a, b, c }"
Tuple elements may be ".*" to indicate no name.  (See also pQualIdOrTuple.)

> pIdOrTuple :: SV_Parser IdOrTuple  -- i.e. a tuple of unqualified identifiers
> pIdOrTuple =
>     pTupleIds <|> pOneId
>   where
>     pTupleIds = do
>         is <- pInBraces $
>                   pCommaSep1 $
>                        do pos <- getPos
>                           pSymbol SV_SYM_dot_star
>                           return (Left pos)
>                       <|>
>                        do i <- pIdentifier <?> "identifier in tuple"
>                           return $ Right i
>         -- XXX a single Just element could be returned as Right
>         return $ Left is
>     pOneId = Right <$> pIdentifier

Parse a task-identifier (starting with $)

> pTaskIdentifier :: SV_Parser Id
> pTaskIdentifier = pToken accept <?> "task identifier"
>     where accept (SV_Token_System_Id { start_position = pos, name = s@(c:d:_) }) =
>               Just (mkId pos (mkFString s))
>           accept _ = Nothing

> pDollar :: SV_Parser ()
> pDollar = pToken accept <?> "dollar"
>     where accept (SV_Token_System_Id { start_position = pos, name = s }) | s=="$" =
>               Just ()
>           accept _ = Nothing

Parse a dot-separated list of identifiers (for long method or rule names)
Note that we allow spaces before and after the dots.

> pCompoundIdentifier :: SV_Parser Longname
> pCompoundIdentifier = pDotSep1 pIdentifier

Parse a comma-separated list of compound identifiers

> pLongnames :: SV_Parser [Longname]
> pLongnames = pCommaSep1 pCompoundIdentifier

Numeric literals (not expressions)

> -- if a leading plus/minus sign is available, this code will handle it;
> -- however, in many situations, the plus/minus is parsed as a unary operator,
> -- in which case "opPrefix" handles it.
> pNumericLiteral :: SV_Parser CExpr
> pNumericLiteral =
>     (try (do pos <- getPos
>              pSymbol SV_SYM_minus
>              li <- pNumericLiteral'
>              case li of
>                CLit (CLiteral _ (LInt (IntLit w l v))) ->
>                    -- XXX when (v == 0) $ parseWarn (pos, WNegativeZeroIntLit)
>                    return (CLit (CLiteral pos (LInt (IntLit w l (-v)))))
>                CLit (CLiteral _ (LReal v)) ->
>                    -- XXX when (v == 0) $ parseWarn (pos, WNegativeZeroIntLit)
>                    return (CLit (CLiteral pos (LReal (-v))))
>                _ -> internalError "pNumericLiteral"))
>    <|>
>     (try (do pos <- getPos
>              pSymbol SV_SYM_plus
>              li <- pNumericLiteral'
>              case li of
>                CLit (CLiteral _ li) -> return (CLit (CLiteral pos li))
>                _ -> internalError "pNumericLiteral"))
>    <|>
>     pNumericLiteral'

> pNumericLiteral' :: SV_Parser CExpr
> pNumericLiteral' = (pToken accept
>                     <|>  (pToken acceptError >>= failWithErr))
>                    <?> "number"
>     where accept (SV_Token_Number { start_position = pos,
>                                     value = SV_NUM_Integer num,
>                                     bitwidth = numWidth,
>                                     base = maybeBase }) =
>               let
>                   -- default base to decimal if not specified
>                   numBase = maybe 10 svNumericBaseValue maybeBase
>                   numLit = CLit $ CLiteral pos $ LInt $
>                            IntLit {ilWidth = numWidth, ilBase = numBase,
>                                    ilValue = num}
>               in  Just numLit
>           accept (SV_Token_Number { start_position = pos,
>                                     value = SV_NUM_Repeated SV_BIT_0,
>                                     base = maybeBase }) =
>               Just (cVar (idConstAllBitsUnsetAt pos))
>           accept (SV_Token_Number { start_position = pos,
>                                     value = SV_NUM_Repeated SV_BIT_1,
>                                     base = maybeBase }) =
>               Just (cVar (idConstAllBitsSetAt pos))
>           accept (SV_Token_Number
>                      { start_position = pos,
>                        value = SV_NUM_Real num,
>                        originalText = txt }) =
>               Just $ CLit $ CLiteral pos $ LReal num
>           accept _ = Nothing
>           acceptError (SV_Token_Number { start_position = pos,
>                                          value = SV_NUM_Repeated _,
>                                          originalText = txt }) =
>               Just (pos, EUnsupportedNumUndetermined txt)
>           acceptError (SV_Token_Number { start_position = pos,
>                                          value = SV_NUM_Mixed bs,
>                                          originalText = txt }) =
>               if (all (not . isXZ . snd) bs)
>               then Just (pos, EMixedLitInNonPatCase txt)
>               else Just (pos, EUnsupportedNumUndetermined txt)
>             where isXZ (Right SV_BIT_X) = True
>                   isXZ (Right SV_BIT_Z) = True
>                   isXZ _ = False
>           acceptError _ = Nothing


Parse any string in quotation marks

> pQuotedString :: SV_Parser String
> pQuotedString = pToken accept <?> "string"
>     where accept (SV_Token_String { start_position = pos,
>                                     contents = str,
>                                     end_position = errPos }) =
>               Just str
>           accept _ = Nothing

Parse a *specific* string, in quotation marks

> pTheQuotedString :: String -> SV_Parser ()
> pTheQuotedString theStr = pToken accept <?> expected
>     where accept (SV_Token_String { start_position = pos,
>                                     end_position = errPos,
>                                     contents = str })
>                  | str == theStr = Just ()
>           accept _ = Nothing
>           -- the token below is constructed only for the purpose
>           -- of pretty-printing it with svTokenToString
>           expected = svTokenToString (SV_Token_String{ start_position = errPos,
>                                     end_position = errPos,
>                                                        contents = theStr })
>           errPos = internalError
>                    ("CVParser.pTheQuotedString: " ++
>                     "svTokenToString forced position")

Parse an integer, in decimal format
XXX actually, this doesn't check that the base is decimal

> pDecimal :: SV_Parser Integer
> pDecimal = pToken accept <?> "decimal number"
>     where accept (SV_Token_Number { start_position = pos,
>                                     value = SV_NUM_Integer val }) = Just val
>           accept _ = Nothing

Parse parentheses around the item accepted by pInside: ( ... )

> pInParens :: SV_Parser item -> SV_Parser item
> pInParens pInside   = do { pSymbol SV_SYM_lparen; inside <- pInside;
>                            pSymbol SV_SYM_rparen; return inside }

Parse parentheses around the item accepted by pInside: ( ... )
Empty parentheses -- save for whitespace -- () or ( ) cause error with errMsg

> pInParensNonEmpty :: EMsg -> SV_Parser item -> SV_Parser item
> pInParensNonEmpty errMsg pInside =
>     pSymbol SV_SYM_lparen >>
>     ((pSymbol SV_SYM_rparen >> failWithErr errMsg)
>      <|> do { inside <- pInside; pSymbol SV_SYM_rparen; return inside })

Parse curly braces around the item accepted by pInside: { ... }

> pInBraces :: SV_Parser item -> SV_Parser item
> pInBraces pInside   = do { pSymbol SV_SYM_lbrace; inside <- pInside;
>                            pSymbol SV_SYM_rbrace; return inside }

Parse square brackets around the item accepted by pInside: [ ... ]

> pInBrackets :: SV_Parser item -> SV_Parser item
> pInBrackets pInside = do { pSymbol SV_SYM_lbracket; inside <- pInside;
>                            pSymbol SV_SYM_rbracket; return inside }

Parse zero or more items accepted by pInside, separated by commas

> pCommaSep :: SV_Parser item -> SV_Parser [item]
> pCommaSep pInside = sepBy pInside (pSymbol SV_SYM_comma)

Parse one or more items accepted by pInside, separated by commas

> pCommaSep1 :: SV_Parser item -> SV_Parser [item]
> pCommaSep1 pInside = sepBy1 pInside (pSymbol SV_SYM_comma)

Parse one or more items accepted by pInside, separated by dots

> pDotSep1 :: SV_Parser item -> SV_Parser [item]
> pDotSep1 pInside = sepBy1 pInside (pSymbol SV_SYM_dot)

Parse ";" and return ()

> pSemi :: SV_Parser ()
> pSemi = pSymbol SV_SYM_semi

Parse ":" and return ()

> pColon :: SV_Parser ()
> pColon = pSymbol SV_SYM_colon

Parse "=" and return ()

> pEq :: SV_Parser ()
> pEq = pSymbol SV_SYM_eq

Parse an uppercase or lowercase identifier, and return it as a string

> pWord :: SV_Parser String
> pWord = pToken accept <?> "identifier"
>     where accept (SV_Token_Id { start_position = pos,
>                               end_position = errPos,
>                               name = s }) = Just s
>           accept _ = Nothing

Parse a VName (a Verilog port name)

> pVName :: SV_Parser V.VName
> pVName = fmap V.VName pWord

Parse a *specific* word

> pTheWord :: Id -> SV_Parser ()
> pTheWord word = pToken accept <?> expected
>     where accept (SV_Token_Id { start_position = pos,
>                               end_position = errPos,
>                               name = s })
>               | s == getIdString word = Just ()
>           accept _ = Nothing
>           expected = svTokenToString
>                      -- the token below is constructed only for the purpose
>                      -- of pretty-printing it with svTokenToString
>                      (SV_Token_Id { start_position = errPos,
>                               end_position = errPos,
>                               name = getIdString word })
>           errPos = internalError
>                    "CVParser.pTheWord: svTokenToString forced position"

Parse a specific word, given as a string

> pTheString :: String -> SV_Parser ()
> pTheString str = pToken accept <?> expected
>     where accept (SV_Token_Id { start_position = pos,
>                               end_position = errPos,
>                               name = s })
>               | s == str = Just ()
>           accept _ = Nothing
>           expected = svTokenToString
>                      -- the token below is constructed only for the purpose
>                      -- of pretty-printing it with svTokenToString
>                      (SV_Token_Id { start_position = errPos,
>                               end_position = errPos,
>                               name = str })
>           errPos = internalError
>                    "CVParser.pTheString: svTokenToString forced position"

Parse specific words, in curly braces

> pTheWords :: [Id] -> SV_Parser ()
> pTheWords [word] = pTheWord word
> pTheWords [] = internalError "empty interface match"
> pTheWords words = pInBraces (mapM_ pTheWord words)

Parse an identifier starting with an uppercase letter and return as string

> pUpperWord :: SV_Parser String
> pUpperWord = pToken accept <?> "identifier starting with uppercase"
>     where accept (SV_Token_Id { start_position = pos,
>                               end_position = errPos,
>                               name = s@(c:_) })
>               | isUpper c = Just s
>           accept _ = Nothing

Parse an identifier (which may or may not be qualified)

> pQualIdentifier :: SV_Parser Id
> pQualIdentifier = try $
>     do pos <- getPos
>        packname <- option (fsEmpty) (try $
>                                      do p <- pUorLIdentifier
>                                         pSymbol SV_SYM_colon_colon
>                                         let (_,fs) = getIdFStrings p
>                                         return fs)
>        theId <- pIdentifier <?> "identifier"
>        let (_, idString) = getIdFStrings theId
>        return $ mkQId pos packname idString

Parse either an identifier or a tuple of IDs (which may or may not be qualified)
Tuple elements may be ".*" to indicate no name.
(This is similar to pIdOrTuple, except for allowing qualifiers.)

> pQualIdOrTuple :: SV_Parser IdOrTuple
> pQualIdOrTuple =
>     pTupleQualIds <|> pOneQualId
>   where
>     pTupleQualIds = do
>       is <- pInBraces $
>               pCommaSep1 $
>                 do pos <- getPos
>                    pSymbol SV_SYM_dot_star
>                    return (Left pos)
>                <|>
>                 do i <- pQualIdentifier <?> "identifier in tuple"
>                    return $ Right i
>       -- XXX a single Just element could be returned as Right
>       return $ Left is
>     pOneQualId = Right <$> pQualIdentifier

Parse a constructor (identifier starting with uppercase), which may or
may not be qualified

> pQualConstructor :: SV_Parser Id
> pQualConstructor = -- try $
>     do pos <- getPos
>        packname <- option (fsEmpty) (try $
>                                      do p <- pUorLIdentifier
>                                         pSymbol SV_SYM_colon_colon
>                                         let (_,fs) = getIdFStrings p
>                                         return fs)
>        name2 <- pUpperWord
>        return (mkQId pos packname (mkFString name2))

Parse an unqualified constructor (identifier starting with uppercase)

> pConstructor :: SV_Parser Id
> pConstructor =
>     do pos <- getPos
>        name <- pUpperWord
>        return (mkId pos (mkFString name))

Parse a numeric constructor (number type)

> pNumberConstructor :: SV_Parser Id
> pNumberConstructor =
>     do pos <- getPos
>        n <- pDecimal <?> "number type"
>        return $ mkId pos (mkFString (show n))

Parse a string constructor (string type)

> pStringConstructor :: SV_Parser Id
> pStringConstructor =
>     do pos <- getPos
>        s <- pQuotedString <?> "string type"
>        return $ mkId pos (mkFString (show s))

Parse a static casting: type ' value

> pCasting :: SV_Parser CExpr
> pCasting =
>   try
>    (do ty <- pTypeExpr
>        pSymbol SV_SYM_tick
>        ex <- pInParens pExpression <|> pBitConcatPrimary
>        return (CHasType ex (CQType [] ty)))

Parse a string literal (quoted string) and return it as an expression

> pStringLiteral :: SV_Parser CExpr
> pStringLiteral =
>   do
>    pos <- getPos
>    s   <- pQuotedString <?> "string"
>    return (stringLiteralAt pos s)

========

Parse 'keyword' and return Nothing, or 'keyword: name' and return Just name

> pStartClause :: SV_Keyword -> SV_Parser (Maybe Id)
> pStartClause keyword =
>     do pKeyword keyword
>        option Nothing (fmap Just (pColon >> pIdentifier))

Parse 'keyword' or 'keyword: identifier', and succeed

> pEndClause :: SV_Keyword -> Maybe Id -> SV_Parser ()
> pEndClause keyword Nothing = pKeyword keyword
> pEndClause keyword (Just identifier) =
>     do pKeyword keyword
>        option () (pColon >> pTheWord identifier >> return ())

> pEndClauseSeq :: SV_Keyword -> Maybe Id -> SV_Parser (Maybe Id)
> pEndClauseSeq keyword Nothing           =
>     do pKeyword keyword
>        option Nothing (fmap Just (pColon >> pIdentifier))
> pEndClauseSeq keyword (Just identifier) =
>     do pKeyword keyword
>        option (Just identifier) (pColon >> pTheWord identifier >> return (Just identifier))


EXPRESSIONS

> pDontCare :: SV_Parser CExpr
> pDontCare =
>     do pos <- getPos
>        pSymbol SV_SYM_question
>        return $ anyExprAt pos

> pVariable :: SV_Parser CExpr
> pVariable = do
>     i <- pQualIdentifier <?> "variable"
>     return $ cVar i

> pParameters :: SV_Parser [CExpr]
> pParameters = option [] (pSymbol SV_SYM_hash >>
>                          pInParens (pCommaSep1 pExpression)) <?> "parameters"

> pTypeConstructor :: SV_Parser CType
> pTypeConstructor =
>     do cons <- ((pNumberConstructor <|> pStringConstructor <|> pQualConstructor)
>                 <?> "type constructor")
>        return (cTCon cons)

> pTypeVariable :: SV_Parser CType
> pTypeVariable = fmap cTVar (pIdentifier <?> "type variable")

Parse a bit range [h:0], for type declarations

> pBitRange :: SV_Parser CType
> pBitRange =
>     do pos <- getPos
>        pInBrackets (pBitRange' pos)

> pBitRange' :: Position -> SV_Parser CType
> pBitRange' pos =
>     do high <- pDecimal <?> "highest bit index"
>        pColon
>        lowPos <- getPos
>        low <- pDecimal <?> "lowest bit index"
>        if low /= 0
>          then failWithErr (lowPos, EUnsupportedBitVector)
>          else return $ cTCon $ mkId pos (mkFString $ show $ high + 1)

Sugar for bit and bit[h:0] types

> pBitType :: SV_Parser CType
> pBitType =
>     do pos <- getPos
>        pKeyword SV_KW_bit
>        let tc1 = cTCon $ mkId pos fs1
>            tcBit = cTCon $ mkQId pos fsPrelude fsBit
>        tcWidth <- option tc1 pBitRange
>        return $ cTApplys tcBit [tcWidth]

Sugar for int type (32-bit signed integers)

> pIntType :: SV_Parser CType
> pIntType =
>     do pos <- getPos
>        pKeyword SV_KW_int
>        return (tInt32At pos)

Sugar for real type (Real)

> pRealType :: SV_Parser CType
> pRealType =
>     do pos <- getPos
>        pKeyword SV_KW_real
>        return (tRealAt pos)

Sugar for void type

> pVoidType :: SV_Parser CType
> pVoidType =
>     do pos <- getPos
>        pKeyword SV_KW_void
>        return (cTCon idPrimUnit)

Sugar for Action type

> pActionType :: SV_Parser CType
> pActionType =
>     do pos <- getPos
>        pKeyword SV_KW_Action
>        return (tActionAt pos)

> pActionValueType :: SV_Parser CType
> pActionValueType =
>     do pos <- getPos
>        pKeyword SV_KW_ActionValue
>        pTypeExprRequiredParamsWith (tActionValueAt pos)


A function type

> pFunctionType :: SV_Parser CType
> pFunctionType =
>     do pos <- getPos
>        prototype <- pFunctionPrototype
>        let (CQType provisos typ) = cf_type prototype
>        when (not (null provisos))
>                 (failWithErr (pos, (EForbiddenProvisos "type")))
>        return typ

The "module" keyword, denoting the current default module monad type

> pDefMonadType :: SV_Parser CType
> pDefMonadType =
>     do pos <- getPos
>        pKeyword SV_KW_module
>        return (TDefMonad pos)

Type parameters: #(type1, type2, ...)

> pTypeParameters :: SV_Parser [CType]
> pTypeParameters = option [] pTypeParametersNonOptional

> pTypeParametersNonOptional :: SV_Parser [CType]
> pTypeParametersNonOptional = do pSymbol SV_SYM_hash
>                                 pInParens (pCommaSep1 pTypeExpr)

Types

> pTypeExpr :: SV_Parser CType
> pTypeExpr =
>         pBitType
>     <|> pIntType
>     <|> pRealType
>     <|> pVoidType
>     <|> pActionType
>     <|> pActionValueType
>     <|> do atype <- ( pTypeConstructor
>                      <|> pTypeVariable
>                      <|> pDefMonadType
>                     ) <?> "type"
>            pTypeExprWith atype
>     <|> pFunctionType
>     <|> pInParens pTypeExpr

Parse parameters for a type expressions and apply

> pTypeExprWith :: CType -> SV_Parser CType
> pTypeExprWith atype =
>     do params <- pTypeParameters <?> "type parameters"
>        return $ cTApplys atype params

> pTypeExprRequiredParamsWith :: CType -> SV_Parser CType
> pTypeExprRequiredParamsWith atype =
>     do params <- pTypeParametersNonOptional <?> "type parameters"
>        return $ cTApplys atype params

Provisos (type constraints)

> pProviso :: SV_Parser CPred
> pProviso =
>     do c <- pQualConstructor
>        pos <- getPos
>        vars <- pTypeParameters
>        when (vars==[])
>                 (failWithErr (pos, (EMissingProvisoArgs (pvpString c))))
>        return (CPred (CTypeclass c) vars)

> pProvisos :: SV_Parser [CPred]
> pProvisos = pKeyword SV_KW_provisos >> pInParens (pCommaSep pProviso)

TYPEDEFS

top level typedef

> pImperativeTypedef :: Attributes -> ImperativeFlags ->
>                       SV_Parser [ImperativeStatement]
> pImperativeTypedef atts flags =
>  do pos <- getPos
>     pKeyword SV_KW_typedef <?> "type definition"
>     when (not (allowTypedef flags)) (failWithErr (pos, EForbiddenTypedef (pvpString (stmtContext flags))))
>     assertEmptyAttributes EAttribsTypedef atts
>     defs <-     fmap (:[]) pTypedefEnum
>             <|> pTypedefStruct
>             <|> pTypedefTaggedUnion
>             <|> fmap (:[]) pTypedefSynonym
>     return [ISTypedef pos defs]

type synonym: typedef <type1>[#(...)] <TypeName>[#(...)];

> pTypedefSynonym :: SV_Parser CDefn
> pTypedefSynonym =
>     do original <- pTypeExpr
>        (synonym, params) <- pTypedefConParams
>        pSemi
>        return $ Ctype synonym params original

enumerated type (like tagged union with void fields)
SV LRM sec 3.10 (of SV 3.1a draft 6)

> pTypedefEnum :: SV_Parser CDefn
> pTypedefEnum =
>     do pKeyword SV_KW_enum
>        summand_pairs <- pInBraces (pEnumTags False 0) <?> "type constructor"
>        name <- pConstructor <?> "enum type name"
>        derivs <- pDerivationsIf True
>        pSemi
>        let (original_summands, internal_summands) = unzip summand_pairs
>        return (Cdata { cd_visible = True,
>                        cd_name = IdK name,
>                        cd_type_vars = [],
>                        cd_original_summands = original_summands,
>                        cd_internal_summands = internal_summands,
>                        cd_derivings = derivs })

XXX allow constants other than decimal

> pEnumTag :: Integer ->
>             SV_Parser (Integer, [(COriginalSummand, CInternalSummand)])
> pEnumTag default_enc =
>     do pos <- getPos
>        name <- pConstructor <?> "enum tag"
>        -- parse the range notation for generating tags with the same prefix
>        range <- option Nothing (Just <$> pInBrackets pEnumRange)
>        -- parse the bit-encoding
>        encoding <- option Nothing (Just <$> (pEq >> pDecimal))
>        let encoding_start = case encoding of
>                             Just n  -> n
>                             Nothing -> default_enc
>        let mk_summand_pair :: Bool -> Integer -> FString
>                            -> (Integer, (COriginalSummand, CInternalSummand))
>            mk_summand_pair is_user_encoding enc postfix =
>                let orig_enc | is_user_encoding = Just enc
>                             | otherwise = Nothing
>                    tag_name = mkIdPost name postfix
>                    summands =
>                        (COriginalSummand { cos_names = [tag_name],
>                                            cos_arg_types = [],
>                                            cos_field_names = Nothing,
>                                            cos_tag_encoding = orig_enc },
>                         CInternalSummand { cis_names = [tag_name],
>                                            cis_arg_type =
>                                                cTCon (idPrimUnitAt pos),
>                                            cis_tag_encoding = enc })
>                in  (enc + 1, summands)
>            postfixes = case range of
>                        Nothing -> [fsEmpty]
>                        (Just (from, to)) ->
>                            let ps | from <= to = [from..to]
>                                   | otherwise  = reverse [to..from]
>                            in  map (mkFString . show) ps
>        return (mapAccumL (mk_summand_pair (isJust encoding))
>                encoding_start postfixes)

> pEnumTags0 :: Bool -> Integer ->
>              SV_Parser [(COriginalSummand, CInternalSummand)]
> pEnumTags0 expect_comma default_enc =
>         do when expect_comma (pSymbol SV_SYM_comma)
>            (next_default_enc, summands) <- pEnumTag default_enc
>            rest_summands <- pEnumTags0 True next_default_enc
>            return (summands ++ rest_summands)
>     <|> return []

> pEnumTags :: Bool -> Integer ->
>              SV_Parser [(COriginalSummand, CInternalSummand)]
> pEnumTags expect_comma default_enc =
>         do p <- getPos
>            x <- pEnumTags0 expect_comma default_enc
>            (when (null x) (failWithErr (p, EEmptyEnum)))
>            return x

> pEnumRange :: SV_Parser (Integer, Integer)
> pEnumRange =
>     do from <- pDecimal <?> "start of enum tag range"
>        (do pColon
>            to <- pDecimal <?> "end of enum tag range"
>            return (from, to)
>         <|>
>         return (0, from-1))

a struct with named and typed fields:
typedef struct { ... } <TypeName>;

> pTypedefStruct :: SV_Parser [CDefn]
> pTypedefStruct =
>     do mkStruct <- pTypedefStructType True
>        let (_, defns) = mkStruct Nothing [] []
>        return defns


toplevel tagged union

> pTypedefTaggedUnion :: SV_Parser [CDefn]
> pTypedefTaggedUnion =
>     do mkTaggedUnion <- pTypedefTaggedUnionType True True
>        let (_, defns) = mkTaggedUnion Nothing [] []
>        return defns

tagged union field: field subtypes, field types

> type TaggedUnionField = (COriginalSummand, CInternalSummand)

if <i> present, make an <i><degree><i'> identifier
otherwise leave <i'>

> mkSubtypeId :: (Maybe Id) -> Id -> Id
> mkSubtypeId Nothing i' = i'
> mkSubtypeId (Just i) i' = mkTCId i i'

type parameter: parameter type <name>

> pTypedefParam :: SV_Parser (Id, PartialKind)
> pTypedefParam =
>     (do option () (pKeyword SV_KW_parameter)
>         pkind <- option PKNoInfo $
>                  (pTheString "numeric" >> return PKNum) <|> -- XXX Seems like these should be an actual keyword?
>                  (pKeyword SV_KW_string >> return PKStr)
>         pKeyword SV_KW_type
>         pid <- pIdentifier
>         return (pid, pkind)
>      ) <?> "type parameter"

type parameters: #(parameter type <name1>, parameter type <name2>, ...)

> pTypedefParams :: SV_Parser [(Id, PartialKind)]
> pTypedefParams = pSymbol SV_SYM_hash >> pInParens (pCommaSep1 pTypedefParam)

optional type parameters
if accept then permit parameters (but accept none)
otherwise don't parse permit type parameters

> pTypedefOptionalParams :: Bool -> SV_Parser [(Id, PartialKind)]
> pTypedefOptionalParams accept =
>     if accept then option [] pTypedefParams else return []


possibly parametrized type constructor

> pTypedefConParams :: SV_Parser (IdK, [Id])
> pTypedefConParams =
>     do name <- pConstructor <?> "type constructor"
>        pks <- option [] pTypedefParams
>        let (params, kinds) = unzip pks
>        let idk = mkIdK name kinds
>        return (idk, params)

function to convert partial kind info into an IdK for defns
(doesn't build a partial kind if there is no info in it,
and doesn't make an assumption about the resulting kind,
though can it ever be anything other than KStar?)

> mkIdK :: Id -> [PartialKind] -> IdK
> mkIdK name [] = IdK name
> mkIdK name kinds | (all (== PKNoInfo) kinds) = IdK name
> mkIdK name kinds = let pkind = foldr PKfun PKNoInfo kinds
>                    in  IdPKind name pkind

optional "deriving (Class, Class, ...)" clause
returns names of classes to be derived, or error if deriving not permitted

> pDerivationsIf :: Bool -> SV_Parser [CTypeclass]
> pDerivationsIf False = option [] $
>     do pos <- getPos
>        pKeyword SV_KW_deriving
>        failWithErr (pos, EForbiddenDeriving)
> pDerivationsIf True = option [] $
>     do pKeyword SV_KW_deriving
>        pInParens (pCommaSep1 (pTypeclass <?> "typeclass name"))


> pTypeclass :: SV_Parser CTypeclass
> pTypeclass = CTypeclass <$> pQualConstructor

STRUCT/UNION NOTE

Most of the struct/tagged-union parsers below return functions which
require a constructor prefix.  This is because, in BSV, the constructor
name is not known until after we've finished parsing the union or struct.

struct field: tagged union or regular type
returns a function which requires a supertype prefix
if prefix is provided, sub-union and sub-struct constructors start with it

> pTypedefStructField ::
>     SV_Parser (Maybe Id {- constructor ID prefix -}
>                -> [(Id, PartialKind)] {- type parameters collected thus far -}
>                -> [CTypeclass] {- derivings collected thus far -}
>                -> (CField, [CDefn] {- accum'd defs -}))
> pTypedefStructField =
>         do mkSubUnion <- pTypedefTaggedUnionType False False
>            let mkField prefix params derivs =
>                    let ((name, fieldConstr, _), defns) =
>                            mkSubUnion prefix params derivs
>                    in  (CField { cf_name = name,
>                                  cf_pragmas = Nothing,
>                                  cf_orig_type = Nothing,
>                                  cf_type = CQType [] fieldConstr,
>                                  cf_default = []
>                                },
>                         defns)
>            return mkField
>     <|> do typ <- fmap (CQType []) pTypeExpr
>            name <- pIdentifier
>            pSemi
>            let field = CField { cf_name = name,
>                                 cf_pragmas = Nothing,
>                                 cf_orig_type = Nothing,
>                                 cf_type = typ,
>                                 cf_default = []
>                               }
>            return (const $ const  $ const (field, []))

many struct fields
returns a function which requires a supertype prefix
if prefix is provided, sub-union and sub-struct constructors start with it

> pTypedefStructFields ::
>     SV_Parser (Maybe Id {- constructor ID prefix -}
>                -> [(Id, PartialKind)] {- type parameters accumulated thus far -}
>                -> [CTypeclass] {- derivations accumulated thus far -}
>                -> [(CField, [CDefn] {- accum'd defs -})])
> pTypedefStructFields =
>     do mks <- many pTypedefStructField
>        let mkFields prefix params derivs =
>                [mk prefix params derivs | mk <- mks]
>        return mkFields

struct definition
returns a function which, given a supertype prefix,
adds the struct def to the accumulated definitions,
and returns its name, type, and field types
if prefix is provided, sub-union and sub-struct constructors start with it

> pTypedefStructType :: Bool {- accept type params? -}
>                    -> SV_Parser
>                       (Maybe Id {- constructor ID prefix -}
>                        -> [(Id, PartialKind)] {- type parameters collected thus far -}
>                        -> [CTypeclass] {- derivations collected thus far -}
>                        -> ((Id, CType, [Id], [CQType]), [CDefn]))
> pTypedefStructType isTopLevel =
>     do pKeyword SV_KW_struct
>        mkFields <- pInBraces pTypedefStructFields
>        name <- pConstructor <?> "struct type name"
>        newParams <- pTypedefOptionalParams isTopLevel
>        newDerivs <- pDerivationsIf isTopLevel
>        pSemi
>        let mkStruct prefix oldParams oldDerivs =
>                let allParams = oldParams ++ newParams
>                    (params, kinds) = unzip allParams
>                    derivs = oldDerivs ++ newDerivs
>                    fullName = mkSubtypeId prefix name
>                    idk = mkIdK fullName kinds
>                    (fields, defns) =
>                        unzip (mkFields (Just fullName) allParams derivs)
>                    fieldNames = map cf_name fields
>                    fieldTypes = map cf_type fields
>                    structType = case prefix of
>                                 Nothing -> SStruct   -- standalone struct
>                                 Just i -> SDataCon i True -- sub-struct
>                    constr = cTApplys (cTCon fullName) (map cTVar params)
>                    defn = Cstruct True structType idk params fields derivs
>                in  ((name, constr, fieldNames, fieldTypes), defn : concat defns)
>        return mkStruct

struct field: sub-struct, tagged union, void, or regular type
returns a function which requires a supertype prefix
if prefix is provided, sub-union and sub-struct constructors start with it

> pTypedefTaggedUnionField ::
>     SV_Parser (Maybe Id {- constructor ID prefix -}
>                -> Integer {- tag encoding -}
>                -> [(Id, PartialKind)] {- type parameters collected thus far -}
>                -> [CTypeclass] {- derivations collected thus far -}
>                -> (TaggedUnionField, [CDefn] {- accum'd defs -}))
> pTypedefTaggedUnionField =
>         do mkSubStruct <- pTypedefStructType False
>            let mkField prefix enc params derivs =
>                    let ((name, typeConstr, fieldNames, fieldTypes), defns) =
>                            mkSubStruct prefix params derivs
>                        original_summands =
>                            COriginalSummand { cos_names = [name],
>                                               cos_arg_types = fieldTypes,
>                                               cos_field_names = Just fieldNames,
>                                               cos_tag_encoding = Nothing }
>                        internal_summands =
>                            CInternalSummand { cis_names = [name],
>                                               cis_arg_type = typeConstr,
>                                               cis_tag_encoding = enc }
>                    in  ((original_summands, internal_summands), defns)
>            return mkField
>     <|> do mkSubUnion <- pTypedefTaggedUnionType False True
>            let mkField prefix enc params derivs =
>                    let ((name, typeConstr, fieldTypes), defns) =
>                            mkSubUnion prefix params derivs
>                        original_summands =
>                            COriginalSummand { cos_names = [name],
>                                               cos_arg_types = fieldTypes,
>                                               cos_field_names = Nothing,
>                                               cos_tag_encoding = Nothing }
>                        internal_summands =
>                            CInternalSummand { cis_names = [name],
>                                               cis_arg_type = typeConstr,
>                                               cis_tag_encoding = enc }
>                    in  ((original_summands, internal_summands), defns)
>            return mkField
>     <|> do pKeyword SV_KW_void
>            name <- pConstructor
>            pSemi
>            let mkField prefix enc params derivs =
>                    let original_summands =
>                            COriginalSummand { cos_names = [name],
>                                               cos_arg_types = [],
>                                               cos_field_names = Nothing,
>                                               cos_tag_encoding = Nothing }
>                        internal_summands =
>                            CInternalSummand { cis_names = [name],
>                                               cis_arg_type = cTCon idPrimUnit,
>                                               cis_tag_encoding = enc }
>                    in ((original_summands, internal_summands), [])
>            return mkField
>     <|> do typ <- pTypeExpr
>            name <- pConstructor
>            pSemi
>            let mkField prefix enc params derivs =
>                    let original_summands =
>                            COriginalSummand { cos_names = [name],
>                                               cos_arg_types = [CQType [] typ],
>                                               cos_field_names = Nothing,
>                                               cos_tag_encoding = Nothing }
>                        internal_summands =
>                            CInternalSummand { cis_names = [name],
>                                               cis_arg_type = typ,
>                                               cis_tag_encoding = enc }
>                    in ((original_summands, internal_summands), [])
>            return mkField

many tagged union fields
returns a function which requires a supertype prefix
if prefix is provided, sub-union and sub-struct constructors start with it

> pTypedefTaggedUnionFields ::
>     SV_Parser (Maybe Id {- constructor ID prefix -}
>                -> [(Id, PartialKind)] {- type parameters collected thus far -}
>                -> [CTypeclass] {- derivations collected thus far -}
>                -> [(TaggedUnionField, [CDefn])])
> pTypedefTaggedUnionFields =
>     do mks <- many1 pTypedefTaggedUnionField
>        let mkFields prefix params derivs =
>                [mk prefix enc params derivs | (mk, enc) <- zip mks [0..]]
>        return mkFields

tagged union definition
returns a function which, given a supertype prefix,
adds the tagged union def to the accumulated definitions,
and returns its name, type, and field types
if prefix is provided, sub-union and sub-struct constructors start with it

if we're parsing a top level tagged union typedef, the name will be a
type name and therefore should be a constructor; otherwise, the name
will be a field inside a struct and should be an identifier

> pTypedefTaggedUnionType :: Bool {- accept type parameters? -}
>                            -> Bool {- should the name be uppercase? -}
>                            -> SV_Parser
>                               (Maybe Id {- constructor ID prefix -}
>                                -> [(Id, PartialKind)] {- type params collected thus far -}
>                                -> [CTypeclass] {- derivations collected thus far -}
>                                -> ((Id, CType, [CQType]), [CDefn]))
> pTypedefTaggedUnionType isTopLevel uppercaseName =
>     do pKeyword SV_KW_union >> pKeyword SV_KW_tagged
>        mkFields <- pInBraces pTypedefTaggedUnionFields
>        name <- (if uppercaseName then pConstructor else pIdentifier)
>        newParams <- pTypedefOptionalParams isTopLevel
>        newDerivs <- pDerivationsIf isTopLevel
>        pSemi
>        let mkResult prefix oldParams oldDerivs =
>                let allParams = oldParams ++ newParams
>                    (params, kinds) = unzip allParams
>                    derivs = oldDerivs ++ newDerivs
>                    fullName = mkSubtypeId prefix name
>                    idk = mkIdK fullName kinds
>                    fields = mkFields (Just fullName) allParams derivs
>                    (summands, defns) = unzip fields
>                    (cosummands, csummands) = unzip summands
>                    defn = Cdata { cd_visible = True,
>                                   cd_name = idk,
>                                   cd_type_vars = params,
>                                   cd_original_summands = cosummands,
>                                   cd_internal_summands = csummands,
>                                   cd_derivings = derivs }
>                    constr = cTApplys (cTCon fullName) (map cTVar params)
>                    fieldtypes = [CQType [] constr]
>                in  ((name, constr, fieldtypes), defn : concat defns)
>        return mkResult


TYPE CLASSES AND INSTANCES

> pDependency :: SV_Parser ([Id],[Id])
> pDependency =
>     do i1s <- fmap (:[]) pIdentifier <|> pInParens (pCommaSep pIdentifier)
>        pTheString "determines"
>        i2s <- fmap (:[]) pIdentifier <|> pInParens (pCommaSep pIdentifier)
>        return (i1s,i2s)

> pDependencies :: SV_Parser [([Id],[Id])]
> pDependencies =
>     do pTheString "dependencies"
>        pInParens (pCommaSep1 pDependency)


> pImperativeTypeclassDecl :: Attributes -> ImperativeFlags
>                          -> SV_Parser [ImperativeStatement]
> pImperativeTypeclassDecl atts flags =
>     do pos <- getPos
>        pKeyword SV_KW_typeclass <?> "typeclass definition"
>        when (not (allowTypeclass flags))
>                 (failWithErr (pos, EForbiddenTypeclass (pvpString (stmtContext flags))))
>        assertEmptyAttributes EAttribsTypeclass atts
>        (name, params) <- pTypedefConParams <?> "typeclass name"
>        context <- option [] pProvisos
>        deps <- option [] pDependencies
>        pSemi
>        functions <- many (pTypeclassFunction <|> pTypeclassModule <|> pTypeclassVarDecl)
>        pEndClause SV_KW_endtypeclass (Just $ iKName name)
>        -- XXX dependencies
>        return [ISTypeclass pos name context deps params functions]

> pTypeclassModule :: SV_Parser CField
> pTypeclassModule =
>           do pos <- getPos
>              pKeyword SV_KW_module <?> "module definition"
>              mCMonadType <-
>                option Nothing
>                       (fmap Just (pInBrackets pTypeExpr))
>              name <- pIdentifier <?> "module name"
>              let (ctxt,tc@(monadType,context')) =
>                      case mCMonadType of
>                        Nothing -> (ISCIsModule, defaultModuleMonadInfo pos)
>                        Just (TDefMonad _) -> (ISCIsModule, defaultModuleMonadInfo pos)
>                        Just t -> (ISCModule t, (t,[]))
>              (params, ifcType, param_props) <- pModuleParams (\ pos -> tc)
>
>              context <- fmap (context' ++) (option [] pProvisos)
>              pSemi
>              defbody <-
>                 ((do pos <- getPos
>                      pKeyword SV_KW_provisos
>                      failWithErr (pos, ESemiBeforeProvisos))
>                  <|>
>                  (do lookAhead (choice [pKeyword SV_KW_function,
>                                         pKeyword SV_KW_module,
>                                         pKeyword SV_KW_endtypeclass])
>                      return [])
>                  <|>
>                  (do let pModEnd = pEndClause SV_KW_endmodule (Just name)
>                      mod <- pModuleBody pos ctxt pModEnd (Just ifcType) []
>                      let (paramIds, _) = unzip params
>                          defClause = CClause (map CPVar paramIds) [] mod
>                      return [defClause]))
>              let resultType = cTApplys monadType [ifcType]
>                  (_, paramTypes) = unzip params
>                  modType = CQType context (foldr fn resultType paramTypes)
>              return (CField { cf_name = name,
>                               cf_pragmas = Nothing,
>                               cf_orig_type = Nothing,
>                               cf_type = modType,
>                               cf_default = defbody
>                             })


> pTypeclassVarDecl :: SV_Parser CField
> pTypeclassVarDecl =
>     do varType <- pTypeExpr
>        varName <- pIdentifier
>        defValue <-
>              do pSymbol SV_SYM_eq
>                 value <- pExpression
>                 return [CClause [] [] value]
>              <|>
>              return []
>        pSemi
>        return (CField { cf_name = varName,
>                         cf_pragmas = Nothing,
>                         cf_orig_type = Nothing,
>                         cf_type = CQType [] varType,
>                         cf_default = defValue
>                       })

> pClassNameType :: SV_Parser (Id, CType)
> pClassNameType =
>     do className <- pConstructor <?> "class name"
>        classType <- pTypeExprWith (cTCon className)
>        return (className, classType)

> pInstanceFunction :: SV_Parser [CDefl]
> pInstanceFunction =
>     do pos <- getPos
>        pKeyword SV_KW_function <?> "function definition"
>        def <- pFunctionAfterKeyword pos
>        return [def]

> pInstanceModule :: SV_Parser [CDefl]
> pInstanceModule =
>     do pos <- getPos
>        let flags = nullImperativeFlags { allowModule = True,
>                                          stmtContext = ISCInstance }
>        modStmts <- pImperativeModule [] flags
>        (Cletseq ds _) <- imperativeToCExpr pos flags modStmts
>        return ds

> pInstanceVar :: SV_Parser [CDefl]
> pInstanceVar =
>     do pos <- getPos
>        varname <- pIdentifier
>        pSymbol SV_SYM_eq
>        value <- pExpression
>        pSemi
>        return [CLValue varname [CClause [] [] value] []]

> pImperativeInstanceDecl :: Attributes -> ImperativeFlags
>                         -> SV_Parser [ImperativeStatement]
> pImperativeInstanceDecl atts flags =
>     do pos <- getPos
>        pKeyword SV_KW_instance <?> "instance definition"
>        when (not (allowInstanceDecl flags))
>                 (failWithErr (pos, EForbiddenInstanceDecl (pvpString (stmtContext flags))))
>        assertEmptyAttributes EAttribsInstance atts
>        (name, classType) <- pClassNameType
>        context <- option [] pProvisos
>        pSemi
>        functions <- fmap concat (many ( pInstanceFunction
>                                        <|> pInstanceModule
>                                        <|> pInstanceVar))
>        pEndClause SV_KW_endinstance (Just name)
>        let classQType = CQType context classType
>        return [ISTypeclassInstance pos classQType functions]

> isClassicDef :: Attribute -> Bool
> isClassicDef (Attribute name (AVString pos classicText)) =
>     getIdString name == "bluespec_classic_def"
> isClassicDef _ = False

> pClassicDefinition :: Attribute -> SV_Parser [ImperativeStatement]
> pClassicDefinition (Attribute name (AVString pos classicText))
>     | getIdString name == "bluespec_classic_def" =
>     do let lflags = Lex.LFlags { Lex.lf_is_stdlib = False,
>                                  Lex.lf_allow_sv_kws = False }
>            classicTokens = Lex.lexStartWithPos lflags pos classicText
>            lexErrs = [(errpos, Lex.convLexErrorToErrMsg err)
>                       | Lex.Token errpos (Lex.L_error err) <- classicTokens]
>        case (lexErrs, Parse.parse CParser.pDefnsAndEOF classicTokens) of
>          (err : _, _) -> failWithErr err -- lexical error
>          (_, Right (results@((defs,x):rest))) ->
>              return [ISClassicDefns pos defs]
>          (_, Right []) -> internalError "CVParser.pClassicDefinition: parse returned Right []"
>          (_, Left (errs, toks)) ->
>              failWithErr (CParser.errSyntax (filter (not . null) errs) toks)
> pClassicDefinition att = internalError ("CVParser.pClassicDefinition: bad bluespec_classic_def attribute:" ++ show att)


INTERFACE DEFINITIONS
(* attribute *)
method Type name ( T1 var, T2 var ) ;

> pMethodPrototype :: Attributes ->  SV_Parser CField
> pMethodPrototype attr =
>     do
>        methodPrags <- attributes2IfcPragmas (False,True) attr
>        --
>        pKeyword SV_KW_method <?> "method definition"
>        rettype <- pTypeExpr <?> "method return type"
>        name <- pIdentifier <?> "method name"
>        args <- option [] (pInParens (pCommaSep (pFunctionArg True) ))
>                <?> "method arguments"
>        context <- option [] pProvisos
>        pSemi
>
>        let (argtypes, rawids, portNameStrings) = unzip3 args
>            argids = zipWith portStringToPrags rawids portNameStrings
>            methtype = CQType context (foldr fn rettype argtypes)
>            duplicateArgs = [(arg1, arg2)
>                             | (arg1:arg2:_) <- group $ sort $ argids]
>        when (not (null duplicateArgs))
>                 (let (arg1, arg2) = head duplicateArgs
>                  in  failWithErr ((getIdPosition arg2),
>                                   (EDuplicateMethodArg (pvpString name)
>                                    (pvpString arg1) (getIdPosition arg1))))
>
>        let
>            duplicatePrags = extractDuplicatePragmas methodPrags
>        when (not (null duplicatePrags)) $
>             do let attr = head duplicatePrags
>                failWithErr ( getPosition name, (EDuplicatePortRenameAttribute attr (getIdString name)))
>
>        return CField { cf_name = name,
>                        cf_pragmas = Just( (PIArgNames argids): methodPrags {-fieldPrags-}),
>                        cf_orig_type = Nothing,
>                        cf_type = methtype,
>                        cf_default = []
>                      }
>        where
>         portStringToPrags :: Id -> Maybe String -> Id
>         portStringToPrags i Nothing  = i
>         portStringToPrags i (Just s) = setIdBaseString i s

(* ifc attributes *)
interface  Top ;
   (* ifc attributes *)
   interface Mid mid1 ;
   interface Mid mid2 ;
endinterface

> pSubinterfacePrototype :: Attributes -> SV_Parser CField
> pSubinterfacePrototype attr =
>     do
>        methodPrags <- attributes2IfcPragmas (False,False) attr
>        --
>        pKeyword SV_KW_interface <?> "subinterface definition"
>        ifcType <- pTypeExpr <?> "subinterface type"
>        name <- pIdentifier <?> "subinterface name"
>        pSemi
>        return CField { cf_name = name,
>                        cf_pragmas = Just methodPrags,
>                        cf_orig_type = Nothing,
>                        cf_type = CQType [] ifcType,
>                        cf_default = []
>                      }

Parse a foreign module port along with its properties
There are separate entrance points for the different types of ports,
since each allowes different sets of attributes:
method enables, method arguments, method ready, and method return values.

> pMethodEnVeriPort :: SV_Parser V.VPort
> pMethodEnVeriPort =
>     let allowed_props = [("inhigh", V.VPinhigh),
>                          ("reg",    V.VPreg),
>                          ("unused", V.VPunused)]
>     in  pVeriPort "a method enable" allowed_props

> pMethodArgVeriPort :: SV_Parser V.VPort
> pMethodArgVeriPort =
>     let allowed_props = [("reg",    V.VPreg),
>                          ("unused", V.VPunused)]
>     in  pVeriPort "a method argument" allowed_props

> pMethodRdyVeriPort :: SV_Parser V.VPort
> pMethodRdyVeriPort =
>     let allowed_props = [("reg",    V.VPreg),
>                          ("const",  V.VPconst)]
>     in  pVeriPort "a method ready" allowed_props

> pMethodValVeriPort :: SV_Parser V.VPort
> pMethodValVeriPort =
>     let allowed_props = [("reg",    V.VPreg),
>                          ("const",  V.VPconst)]
>     in  pVeriPort "a method output" allowed_props

This is the generic function of which the above functions are the
specific entrance points

> pVeriPort :: String -> [(String, V.VeriPortProp)] -> SV_Parser V.VPort
> pVeriPort loc allowed_props =
>     do props <- option [] (do pSymbol SV_SYM_lparen_star
>                               ps <- pCommaSep (pVeriProp loc allowed_props)
>                               pSymbol SV_SYM_star_rparen
>                               return ps)
>        portName <- pVName
>        return (portName, props)

> pVeriProp :: String -> [(String, V.VeriPortProp)] -> SV_Parser V.VeriPortProp
> pVeriProp loc allowed_props = do
>     pos <- getPos
>     -- unfortunately, the lexer tokenizes 'reg' and 'const' inside '(*'
>     -- this code works, but the error message when the user writes e.g.
>     -- (* this *) is about the keyword and not that "this" isn't a property
>     propString <- (pKeyword SV_KW_reg >> return "reg")
>                    <|>
>                    (pKeyword SV_KW_const >> return "const")
>                    <|>
>                    (pWord <?> "property")
>     case (lookup propString allowed_props) of
>         Nothing -> let allowed_strs = map fst allowed_props
>                    in  -- if we want to be complete, we can keep a list of
>                        -- all possible port props and report a different
>                        -- error for unknown port props vs the port prop
>                        -- not allowed on this type of port
>                        failWithErr
>                          (pos, EBadPortProperty loc propString allowed_strs)
>         Just p  -> return p


> isJustAction :: Maybe CType -> Bool
> isJustAction (Just (TCon (TyCon i _ _))) = i == idAction
> isJustAction _ = False
>
> isJustAorAV :: Maybe CType -> Bool
> isJustAorAV (Just (TCon (TyCon i _ _))) = i == idAction
> isJustAorAV (Just (TAp (TCon (TyCon i _ _)) _)) = i == idActionValue
> isJustAorAV _ = False

> data MethodOption = Enable | Ready | ClockedBy | ResetBy
>                        deriving (Eq, Ord)
> data MOdata = VeriPt V.VPort | Ident Id
>                        deriving (Eq)

The following reads a long name (i.e. a dot-separated list of identifiers, and
returns a single identifier formed by joining the components with underscores.

> pDottedName :: SV_Parser Id
> pDottedName = foldr1 mkUSId <$> pCompoundIdentifier


> pMethodOption :: SV_Parser (MethodOption, MOdata)
> pMethodOption =
>     ((do pTheString "ready"
>          p <- pInParens pMethodRdyVeriPort
>          return (Ready, VeriPt p))
>      <|>
>      (do pTheString "enable"
>          p <- pInParens pMethodEnVeriPort
>          return (Enable, VeriPt p))
>      <|>
>      (do pKeyword SV_KW_clocked_by
>          i <- pInParens pDottedName
>          return (ClockedBy, Ident i))
>      <|>
>      (do pKeyword SV_KW_reset_by
>          i <- pInParens pDottedName
>          return (ResetBy, Ident i))
>      <?> "optional component of method")

> pMethodVeriProt ::  Id -> SV_Parser [ (Id,V.VFieldInfo,Bool)] -- "method" keyword already read
>             -- Id is short name; prefixed name is used in VFieldInfo component
>             -- Bool indicates whether there's a separate Ready method for this one
> pMethodVeriProt prefix =
>     do pos <- getPos
>        (optOPort, name) <- pMethodNameOptOPort <?> "method output port or name"
>        multi <- option 1 (pInBrackets pDecimal)
>        args <- (option [] (pInParens (pCommaSep pMethodArgVeriPort))
>                 <?> "method arguments")
>        opts <- many pMethodOption
>        pSemi
>        let nstr = getIdBaseString name
>        when (nstr == "enable" ||
>              nstr == "ready" ||
>              nstr == "clocked_by" ||
>              nstr == "reset_by")
>             (parseWarn (pos, WPerhapsBadMethodName nstr))
>        let fullname = mkUSId prefix name
>        let lookupOpt o =
>                case (lookup o (joinByFst opts)) of
>                    Nothing  -> return Nothing
>                    Just [v] -> return (Just v)
>                    Just []  -> internalError "pMethodVeriProt(0)"
>                    Just vs  -> let str = case o of
>                                            ClockedBy -> "clocked_by"
>                                            ResetBy -> "reset_by"
>                                            Enable -> "enable"
>                                            Ready -> "ready"
>                                in failWithErr (pos, EBVIMultipleOpts str)
>        mclk <- lookupOpt ClockedBy
>        mrst <- lookupOpt ResetBy
>        men  <- lookupOpt Enable
>        mrdy <- lookupOpt Ready
>        let clk = case mclk of
>                      Nothing -> Nothing
>                      Just (Ident i) -> Just i
>                      Just _ -> internalError "pMethodVeriProt(1)"
>            rst = case mrst of
>                      Nothing -> Nothing
>                      Just (Ident i) -> Just i
>                      Just _ -> internalError "pMethodVeriProt(2)"
>            en = case men of
>                      Nothing -> Nothing
>                      Just (VeriPt p) -> Just p
>                      Just _ -> internalError "pMethodVeriProt(3)"
>            nullOrReady = case mrdy of
>                            Nothing -> []
>                            Just (VeriPt p) ->
>                              [(mkRdyId name,
>                                V.Method (mkRdyId fullname)
>                                    clk rst 0 [] (Just p) Nothing,
>                                False)]
>                            Just _ -> internalError "pMethodVeriProt(4)"
>        return ((name,
>                 V.Method fullname
>                          clk
>                          rst
>                          multi
>                          args
>                          optOPort
>                          en,
>                  not(null nullOrReady))
>                : nullOrReady)
>

> pImperativeInterfaceDeclOrSubinterface :: Attributes -> ImperativeFlags
>                                        -> SV_Parser [ImperativeStatement]
> pImperativeInterfaceDeclOrSubinterface atts flags =
>     do pos <- getPos
>        pKeyword SV_KW_interface <?> "interface"
>        -- jes
>        let bools = (allowInterface flags, allowSubinterface flags, allowNakedExpr flags)
>        case bools of
>           (False,False,False) ->
>                (failWithErr (pos, EForbiddenInterface (pvpString (stmtContext flags))))
>           (True,False,False) -> pImperativeInterfaceDeclAt atts flags pos
>           (False,True,_) -> pImperativeSubinterfaceAt atts flags pos
>           (False,False,True) -> do
>                         assertEmptyAttributes EAttribsThisDecl atts
>                         e <- pInterfaceAfterKW pos
>                         return [ISNakedExpr pos e]
>           _ -> (internalError
>                 ("CVParser.pImperativeInterfaceDeclOrSubinterface: " ++
>                   "more than one kind of interface permitted, ambiguous"))

> pImperativeInterfaceDeclAt :: Attributes -> ImperativeFlags -> Position
>                            -> SV_Parser [ImperativeStatement]
> pImperativeInterfaceDeclAt atts flags pos =
>     do topIfcPragmas <- attributes2IfcPragmas (True,False)  atts
>        (name, params) <- pTypedefConParams <?> "interface type"
>        pSemi
>        methods <- many (do  attrs <- pAttributes ;
>                             pMethodPrototype attrs <|> pSubinterfacePrototype attrs)
>        pEndClause SV_KW_endinterface (Just $ iKName name)
>        return [ISInterface pos name topIfcPragmas params methods]

Subinterface -- an interface field inside another interface

> pImperativeSubinterfaceAt :: Attributes -> ImperativeFlags -> Position
>                           -> SV_Parser [ImperativeStatement]
> pImperativeSubinterfaceAt atts flags interfacePos =
>     do constr <- option Nothing (Just <$> pQualConstructor)
>        name <- pIdentifier <?> "subinterface name"
>        (pImperativeSubinterfaceSemiAt atts flags interfacePos constr name
>         <|> pImperativeSubinterfaceEqAt atts flags interfacePos name)

> pImperativeSubinterfaceEqAt :: Attributes -> ImperativeFlags -> Position
>                             -> Id -- field name
>                             -> SV_Parser [ImperativeStatement]
> pImperativeSubinterfaceEqAt atts flags interfacePos name =
>     do pEq
>        ifcExpr <- pExpression
>        pSemi
>        let def = CLValue name [CClause [] [] ifcExpr] []
>        -- XXX support attributes?
>        assertEmptyAttributes EAttribsThisDecl atts
>        return [ISMethod interfacePos def]

> pImperativeSubinterfaceSemiAt :: Attributes -> ImperativeFlags -> Position
>                               -> Maybe Id -- ifc constructor -- required
>                               -> Id -- field name
>                               -> SV_Parser [ImperativeStatement]
> pImperativeSubinterfaceSemiAt atts flags interfacePos maybeConstr name =
>     do pSemi
>        let err = ESyntax ("identifier " ++ quote (pvpString name))
>                  ["interface tag"]
>        when (isNothing maybeConstr) (failWithErr (getPosition name, err))
>        let constr = fromJustOrErr -- guarded by when (isNothing) above
>                     "CVParser.pImperativeSubinterfaceSemiAt: missing tag"
>                     maybeConstr
>            flags = (nullImperativeFlags { stmtContext = ISCInterface,
>                                           -- allow defining bound expressions
>                                           allowEq = True,
>                                           allowSubscriptAssign = True,
>                                           allowFieldAssign = True,
>                                           allowLet = True,
>                                           allowFunction = True,
>                                           allowConditionals = True,
>                                           allowLoops = True,
>                                           allowModule = True,
>                                           allowArrayDecl = True,
>                                           -- allow interface specific stmts
>                                           allowMethod = True,
>                                           allowSubinterface = True })
>        body <- pImperativeExprBlock interfacePos [] flags
>        pEndClause SV_KW_endinterface (Just name)
>        let
>            fixIfcPosAndCtor (Cinterface _ Nothing methods) =
>                Cinterface interfacePos (Just constr) methods
>            fixIfcPosAndCtor (Cletseq defls expr) =
>                Cletseq defls (fixIfcPosAndCtor expr)
>            fixIfcPosAndCtor (Cletrec defls expr) =
>                Cletrec defls (fixIfcPosAndCtor expr)
>            fixIfcPosAndCtor expr =
>                internalError ("CVParser.pImperativeSubinterfaceSemiAt: " ++
>                               "bad expression:\n" ++ show expr)
>            -- fixup the position and insert the ifc constructor name
>            bodyWithBetterPos = fixIfcPosAndCtor body
>            def = CLValue name [CClause [] [] bodyWithBetterPos] []
>        -- XXX support attributes?
>        assertEmptyAttributes EAttribsThisDecl atts
>        return [ISMethod interfacePos def]

INTERFACE EXPRESSIONS

> pInterfacePrimary :: SV_Parser CExpr
> pInterfacePrimary =
>     do interfacePos <- getPos
>        pKeyword SV_KW_interface
>        pInterfaceAfterKW interfacePos -- jes
>
> pInterfaceAfterKW :: Position -> SV_Parser CExpr --jes
> pInterfaceAfterKW interfacePos =
>     do name <- pQualConstructor <?> "interface tag"
>        _ <- pTypeExprWith (cTCon name)
>        option () pSemi;
>        let flags = (nullImperativeFlags { stmtContext = ISCInterface,
>                                           -- allow defining bound expressions
>                                           allowEq = True,
>                                           allowSubscriptAssign = True,
>                                           allowFieldAssign = True,
>                                           allowLet = True,
>                                           allowFunction = True,
>                                           allowConditionals = True,
>                                           allowLoops = True,
>                                           allowModule = True,
>                                           allowArrayDecl = True,
>                                           -- allow interface specific stmts
>                                           allowMethod = True,
>                                           allowSubinterface = True })
>        expr <- pImperativeExprBlock interfacePos [] flags
>        pEndClause SV_KW_endinterface (Just name)
>        let
>            fixIfcPosAndCtor (Cinterface _ Nothing methods) =
>                Cinterface interfacePos (Just name) methods
>            fixIfcPosAndCtor (Cletseq defls e) =
>                Cletseq defls (fixIfcPosAndCtor e)
>            fixIfcPosAndCtor (Cletrec defls e) =
>                Cletrec defls (fixIfcPosAndCtor e)
>            fixIfcPosAndCtor e =
>                internalError ("CVParser.pInterfacePrimary: " ++
>                               "bad expression:\n" ++ ppReadable e)
>        return (fixIfcPosAndCtor expr)

> pRulesPrimary :: SV_Parser CExpr
> pRulesPrimary =
>     do rulesPos <- getPos
>        as <- pAttributes
>        name <- pStartClause SV_KW_rules
>        let flags = (nullImperativeFlags { stmtContext = ISCRules,
>                                           -- allow defining bound expressions
>                                           allowEq = True,
>                                           allowSubscriptAssign = True,
>                                           allowFieldAssign = True,
>                                           allowLet = True,
>                                           allowFunction = True,
>                                           allowConditionals = True,
>                                           allowLoops = True,
>                                           allowModule = True,
>                                           allowArrayDecl = True,
>                                           -- allow rules specific stmts
>                                           allowRule = True })
>        expr <- pImperativeExprBlock rulesPos [] flags
>        pEndClause SV_KW_endrules name
>        -- We allow all the sprags, but for rprag we only allow "doc"
>        -- (That is, we don't propagate the single-rule pragmas to each
>        -- rule in the `rules..endrules' block.)
>        let allowed = -- rprags
>                      ["doc"] ++
>                      -- sprags
>                      ["descending_urgency", "execution_order", "preempts",
>                       "mutually_exclusive", "conflict_free"]
>            hidden  = -- rprags
>                      [""] ++
>                      -- sprags
>                      ["scheduling"]
>            loc = "a `rules..endrules' expression"
>        _ <- reportBadAttributeName loc allowed hidden as
>        (rprags, sprags) <- attributes2rprags as
>        let attachRPrags (CRule rps n q e) =
>              CRule (rprags ++ rps) n q e
>            attachRPrags (CRuleNest rps n q rs) =
>              CRuleNest (rprags ++ rps) n q rs
>        let attachSPrags (Crules prags rules) =
>              (Crules (prags++sprags) (map attachRPrags rules))
>            attachSPrags (Cletrec defs body) =
>              (Cletrec defs (attachSPrags body))
>            attachSPrags (Cletseq defs body) =
>              (Cletseq defs (attachSPrags body))
>            attachSPrags _ = internalError "pRulesPrimary"
>        return (attachSPrags expr)

> pCasePrimary :: SV_Parser CExpr
> pCasePrimary =
>     do casePos <- getPos
>        let flags = (nullImperativeFlags { allowEq = True,
>                                           allowSubscriptAssign = True,
>                                           allowFieldAssign = True,
>                                           allowArrayDecl = True,
>                                           allowLoops = True,
>                                           allowConditionals = True,
>                                           allowFunction = True,
>                                           allowReturn = True,
>                                           allowModule = True,
>                                           allowLet = True,
>                                           allowNakedExpr = True,  -- jes
>                                           stmtContext = ISCExpression })
>        stmts <- pImperativeCase [] flags
>        imperativeToCExpr casePos flags stmts

EXPRESSIONS

> pConstructorPrimary :: SV_Parser CExpr
> pConstructorPrimary =
>     ( (do pKeyword SV_KW_tagged
>           name <- pQualConstructor
>           pConstructorPrimaryWith name True)
>       <|>
>       (do name <- pQualConstructor
>           pConstructorPrimaryWith name False))

> pConstructorPrimaryWith :: Id -> Bool -> SV_Parser CExpr
> pConstructorPrimaryWith name tagged =
>         do namedArgs <- pInBraces (pCommaSep pFieldInit)
>            return $ CStruct (Just (not tagged)) name namedArgs
>     <|> do positionalArgs <- option [] (pConstructorPrimaryPositionalArgs tagged)
>            return $ CCon name positionalArgs

> pConstructorPrimaryPositionalArgs :: Bool -> SV_Parser [CExpr]
> pConstructorPrimaryPositionalArgs tagged =
>         ( (pInParens (pCommaSep pExpression))
>          <|>
>           (do when (not tagged) (fail "tagged expression")
>               (fmap (:[]) (pPrimaryCaring False))))

> pFieldInit :: SV_Parser (Id, CExpr)
> pFieldInit =
>     do name <- pIdentifier
>        pColon
>        value <- pExpression
>        return (name, value)

primary with arguments, e.g. prim(a,b,c)

> pPrimaryWithArgs :: CExpr -> SV_Parser CExpr
> pPrimaryWithArgs e =
>--     do args <- many1 (pInParens (pCommaSep pExpression))
>     do pos <- getPos
>        amcmrmps <- many1 pPortListArgs
>        let ((args, mClock, mReset, mPower),ok) =
>              case amcmrmps of
>                    [x] -> (x,True)
>                    xs  -> let p(_,Nothing,Nothing,Nothing) = True
>                               p _ = False
>                               q (x,_,_,_) = x
>                           in  ((concat (map q xs),Nothing,Nothing,Nothing),
>                                all p xs)
>            e'' = cApply 17 e args
>            e'   = (if isNothing mClock && isNothing mReset && isNothing mPower
>                            then e''
>                            else cVApply (idChangeSpecialWires (getPosition e''))
>                                         [mkMaybe mClock,
>                                          mkMaybe mReset,
>                                          mkMaybe mPower,
>                                          e''])
>        (when (not ok)
>              (failWithErr (pos, EBadSpecialArgs)))
>        (pPrimaryWithFields e'
>         <|> pPrimaryWithBitSel e'
>         <|> return e')

parse suffix .method1 .method2 .Tag1 etc

> pPrimaryWithFields :: CExpr -> SV_Parser CExpr
> pPrimaryWithFields e =
>     do let pIdentifierOrTag =
>                (Left <$> pQualIdentifier)
>                <|> (Right <$> pConstructor)
>            mkSelect expr (Left name) = CSelect expr name
>            mkSelect expr (Right tag) =
>                -- translate to: case expr of Tag var -> var
>                let pos = getPosition tag
>                    result = idTheResult pos
>                in  Ccase pos expr
>                        [CCaseArm { cca_pattern = CPCon tag [CPVar result],
>                                    cca_filters = [],
>                                    cca_consequent = cVar result }]
>        selects <- many1 (pSymbol SV_SYM_dot >> pIdentifierOrTag)
>        let e' = foldl mkSelect e selects
>        pPrimaryWithArgs e' <|> pPrimaryWithBitSel e' <|> return e'

parse suffix for bit selection [N:M] (where N >= M) or [N]

> pPrimaryWithBitSel :: CExpr -> SV_Parser CExpr
> pPrimaryWithBitSel expr =
>     do pos <- getPos
>        es <- many1 (pInBrackets pBitSelSubscript)
>        let mkSel object (Left subscr) = CSub pos object subscr
>            mkSel object (Right (high, low)) = CSub2 object high low
>            e' = (foldl mkSel expr es)
>        pPrimaryWithFields e' <|> pPrimaryWithArgs e' <|> return e'

> pBitSelSubscript :: SV_Parser (Either CExpr (CExpr, CExpr))
> pBitSelSubscript = pExpression >>= pBitSelSubscriptWith

> pBitSelSubscriptWith :: CExpr -> SV_Parser (Either CExpr (CExpr, CExpr))
> pBitSelSubscriptWith e1 =
>         do pColon
>            e2 <- pExpression
>            return (Right (e1,e2))
>     <|> return (Left e1)

task call

> pTaskCallPrimary :: SV_Parser CExpr
> pTaskCallPrimary =
>     do taskName <- pTaskIdentifier <?> "task call"
>        pTaskCallPrimaryWith taskName

> pTaskCallPrimaryWith :: Id -> SV_Parser CExpr
> pTaskCallPrimaryWith taskName =
>         do args <- pInParens (pCommaSep pExpression)
>            return (CTaskApply (CVar taskName) args)
>     <|> return (CTaskApply (CVar taskName) [])

parse suffix: function call or select or combination thereof

> pPrimaryWithSuffix :: CExpr -> SV_Parser CExpr
> pPrimaryWithSuffix e =  pPrimaryWithFields e
>                     <|> pPrimaryWithArgs e
>                     <|> pPrimaryWithBitSel e
>                     <|> return e

> -- this returns the position *after* the expression
> -- (for instance, used in concat to find the position of the commas)
> pExpPos :: SV_Parser (CExpr, Position)
> pExpPos =
>     do e <- pExpression
>        p <- getPos
>        return (e,p)

> pBitConcatPrimary :: SV_Parser CExpr
> pBitConcatPrimary =
>     do expPoses <- pInBraces (pCommaSep1 pExpPos)
>                       <?> "bit concatenation"
>        let catAt pos = cVar (idPrimConcatAt pos)
>            cat (e,p) (es,_) = (cApply 19 (catAt p) [e, es], p)
>            (ex, _) = foldr1 cat expPoses
>        return ex

parse valueOf and stringOf: these are like function call, but applied to a type

> pValueOf :: SV_Parser CExpr
> pValueOf =
>     do p <- getPos
>        (pKeyword SV_KW_valueOf <|> pKeyword SV_KW_valueof)
>        ty <- pInParens pTypeExpr
>        return (cVApply (setIdPosition p idValueOf)
>                [CHasType (anyExprAt p)
>                 (CQType [] (TAp (cTCon idBit) ty))])

> pStringOf :: SV_Parser CExpr
> pStringOf =
>     do p <- getPos
>        (pKeyword SV_KW_stringOf <|> pKeyword SV_KW_stringof)
>        ty <- pInParens pTypeExpr
>        return (cVApply (setIdPosition p idStringOf)
>                [CHasType (anyExprAt p)
>                 (CQType [] (TAp (cTCon idStringProxy) ty))])

> pPrimary :: SV_Parser CExpr
> pPrimary = pPrimaryCaring True

> pPrimaryCaring :: Bool -> SV_Parser CExpr
> pPrimaryCaring allowDontCare
>     =  ((pNumericLiteral >>= pPrimaryWithSuffix)
>         <|> pStringLiteral
>         <|> pCasting
>         <|> pActionExpr
>         <|> pActionValueExpr
>         <|> pSequenceExpr
>         <|> pInterfacePrimary
>         <|> pRulesPrimary
>         <|> pCasePrimary
>         <|> pBitConcatPrimary
>         <|> pImperativeExpression
>         <|> pModuleExpression
>         <|> pTaskCallPrimary
>         <|> pValueOf
>         <|> pStringOf
>         -- variable, function call, method select
>         <|> ((if allowDontCare
>               then pVariable <|> pDontCare <|> pInParens pExpression
>               else pVariable <|> pInParens pExpression)
>              >>= pPrimaryWithSuffix)
>         <|> pConstructorPrimary)
>        <?> "expression"
>


FAUX IMPERATIVE BLOCKS

XXX permit if- and case- statements after interface declaration?

> pImperativeExprBlock :: Position -> Attributes -> ImperativeFlags -> SV_Parser CExpr
> pImperativeExprBlock startPos [] flags =
>     do stmts <- pImperativeStmts flags
>        imperativeToCExpr startPos flags stmts

if we have parsed attributes, then we must parse at least one statement,
to which we attach those attributes

> pImperativeExprBlock startPos attrs flags =
>     do first <- pImperativeStmtWithAttrs attrs flags
>        rest  <- pImperativeStmts flags
>        imperativeToCExpr startPos flags (first ++ rest)

> pImperativeStmtBlock :: ImperativeFlags -> SV_Parser () -> SV_Parser [CStmt]
> pImperativeStmtBlock flags pBlockEnd =
>     do stmts <- pImperativeStmts flags
>        -- check that the block fully parses before converting the body
>        -- (which might prematurely report errors about missing interface, etc)
>        pBlockEnd
>        imperativeToCStmts (stmtContext flags, ifcType flags, filestr flags) stmts

> pImperativeStmt :: ImperativeFlags -> SV_Parser [ImperativeStatement]
> pImperativeStmt flags = do
>   attrs <- pAttributes
>   pImperativeStmtWithAttrs attrs flags

> pImperativeStmtWithAttrs  :: Attributes -> ImperativeFlags -> SV_Parser [ImperativeStatement]
> pImperativeStmtWithAttrs orig_atts flags  = do
>     let (classic_defs, atts1) = partition isClassicDef orig_atts
>     classic_stmts <- concat <$> mapM pClassicDefinition classic_defs
>     (splitness, atts) <- splitInAttributes atts1
>     stmts <-    pImperativeBVI atts flags
>             <|> pImperativeModule atts flags
>             <|> pImperativeReturn atts flags
>             <|> pImperativeFunction atts flags
>             <|> pImperativeRule atts flags
>             <|> pImperativeMethod atts flags
>             <|> pImperativeIf atts flags
>             <|> pImperativeAbtIf atts flags
>             <|> pImperativeCase atts flags
>             <|> pImperativeRepeat atts flags
>             <|> pImperativeWhile atts flags
>             <|> pImperativeFor atts flags
>             <|> pImperativeTaskCall atts flags
>             <|> pImperativeBreak atts flags
>             <|> pImperativeContinue atts flags
>             <|> pImperativeGoto atts flags
>             <|> pImperativeTypedef atts flags
>             <|> pImperativeImportOrForeign atts flags
>             <|> pImperativeExport atts flags
>             <|> pImperativeInterfaceDeclOrSubinterface atts flags
>             <|> pImperativeTypeclassDecl atts flags
>             <|> pImperativeInstanceDecl atts flags
>             <|> pImperativeNested atts flags
>             <|> pAssertionWithLabel atts flags
>             <|> pImperativeDeclOrAssignSemi atts flags
>             -- The following must come after the previous line, because it
>             -- sometimes deliberately fails, to leave something for them to
>             -- cope with
>             <|> pSequence atts flags
>             <|> pProperty atts flags
>             <|> pAssertion atts flags
>             <?> "statement"
>     case splitness of
>       Nothing -> return (classic_stmts ++ stmts)
>       Just wrapper
>         -> do pos <- getPos
>               let pos_error = getPosition stmts
>               let updated = getUFVISs stmts
>               let split = wrapper == idSplitDeepAV
>               let vars = map getIdString (S.toList updated)
>               let actionCtx = isActionContext (stmtContext flags)
>               when (not actionCtx) $ failWithErr (pos_error, ESplitAttrNonActionCtx split)
>               when ((not . S.null) updated) $ failWithErr (pos_error, (ESplitAttrUpd split vars))
>               mapM_ (chkSplitStmts split) stmts
>               expr <- imperativeToCExprForSplitAttribute pos flags stmts
>               return (classic_stmts ++
>                       [(ISNakedExpr pos (wrapIf wrapper expr))])
>


> chkSplitStmts :: Bool -> ImperativeStatement -> SV_Parser ()
> chkSplitStmts _ (ISUpdateReg {}) = return ()
> chkSplitStmts _ (ISRegWrite {}) = return ()
> chkSplitStmts _ (ISNakedExpr {}) = return ()
> chkSplitStmts _ (ISFor {}) = return ()
> chkSplitStmts _ (ISWhile {}) = return ()
> chkSplitStmts _ (ISBeginEnd {}) = return ()
> chkSplitStmts _ (ISAction {}) = return ()
> chkSplitStmts _ (ISIf {}) = return ()
> chkSplitStmts _ (ISCase {}) = return ()
> chkSplitStmts _ (ISCaseTagged {}) = return ()
> chkSplitStmts _ (ISActionValue {}) = return ()
> chkSplitStmts split stmt@(ISReturn {}) = failWithErr (getPosition stmt, ESplitAttrReturn split)
> chkSplitStmts split stmt@(ISDecl {}) = failWithErr (getPosition stmt, ESplitAttrBinding split)
> chkSplitStmts split stmt@(ISPatEq {}) = failWithErr (getPosition stmt, ESplitAttrBinding split)
> chkSplitStmts split stmt@(ISPatBind {}) = failWithErr (getPosition stmt, ESplitAttrBinding split)
> chkSplitStmts split stmt@(ISBind {}) = failWithErr (getPosition stmt, ESplitAttrBinding split)
> chkSplitStmts split stmt@(ISFunction {}) = failWithErr (getPosition stmt, ESplitAttrBinding split)
> chkSplitStmts split stmt = internalError ("chkSplitStmts unexpected: " ++ pvpReadable stmt)


> pImperativeStmts :: ImperativeFlags -> SV_Parser [ImperativeStatement]
> pImperativeStmts flags = fmap concat (many (pImperativeStmt flags))

> pImperativeNested :: Attributes -> ImperativeFlags
>                   -> SV_Parser [ImperativeStatement]
> pImperativeNested atts flags =
>         pImperativeNestedBeginEnd atts flags
>     <|> pImperativeNestedAction atts flags
>     <|> pImperativeNestedActionValue atts flags
>     <|> pImperativeNestedSeq atts flags
>     <|> pImperativeNestedPar atts flags

> pImperativeNestedBeginEnd :: Attributes -> ImperativeFlags
>                           -> SV_Parser [ImperativeStatement]
> pImperativeNestedBeginEnd atts flags =
>     do pos <- getPos
>        name <- pStartClause SV_KW_begin
>        let ctxt = stmtContext flags
>        when (ctxt == ISCSequence)
>             (failWithErr (pos, ESequenceRequired (pvpString (stmtContext flags))))
>        assertEmptyAttributes EAttribsBeginEnd atts
>        stmts <- pImperativeStmts flags
>        pEndClause SV_KW_end name
>        return [ISBeginEnd pos stmts]

> pImperativeNestedSeq :: Attributes -> ImperativeFlags
>                      -> SV_Parser [ImperativeStatement]
> pImperativeNestedSeq atts flags =
>     do pos <- getPos
>        name <- pStartClause SV_KW_seq
>        pImperativeNestedSeqPar2 pos True name atts flags

> pImperativeNestedPar :: Attributes -> ImperativeFlags
>                      -> SV_Parser [ImperativeStatement]
> pImperativeNestedPar atts flags =
>     do pos <- getPos
>        name <- pStartClause SV_KW_par
>        pImperativeNestedSeqPar2 pos False name atts flags

> pImperativeNestedSeqPar2 :: Position -> Bool -> (Maybe Id)
>                          -> Attributes -> ImperativeFlags
>                          -> SV_Parser [ImperativeStatement]
> pImperativeNestedSeqPar2 pos isSeq name atts flags =
>     do let ctxt = stmtContext flags
>        when (ctxt /= ISCSequence && ctxt /= ISCExpression) -- jes
>             (failWithErr (pos, EForbiddenSequence (pvpString (stmtContext flags))))
>        assertEmptyAttributes EAttribsSeq atts
>        let seqFlags = (nullImperativeFlags { stmtContext = ISCSequence,
>                                              allowBind = True,
>                                              allowLoops = True,
>                                              allowConditionals = True,
>                                              allowReturn = True,
>                                              allowNakedExpr = True,
>                                              allowSubscriptAssign = True,
>                                              allowFieldAssign = True,
>                                              allowRegWrite = True })
>
>        stmts <- pImperativeStmts seqFlags
>        let createStmt True  Nothing   = (ISSeq pos stmts)
>            createStmt False Nothing   = (ISPar pos stmts)
>            createStmt True  (Just id) = (ISNamed pos id [(ISSeq pos stmts)])
>            createStmt False (Just id) = (ISNamed pos id [(ISPar pos stmts)])
>
>        if (ctxt == ISCSequence)
>         then do nm <- pEndClauseSeq (if isSeq then SV_KW_endseq else SV_KW_endpar) name
>                 return [(createStmt isSeq nm)] -- jes
>         else do -- naked expression case:
>           pEndClause (if isSeq then SV_KW_endseq else SV_KW_endpar) name
>           stmtts <- imperativeToStmtSeq ISCSequence stmts
>           pSemi
>           let ps = posToString pos
>               theId = if isSeq then idSSeq else idSPar
>           return [ISReturn pos
>                    (Just (cVApply (idSprime pos) [CCon (theId pos) [ps, stmtts]]))]

> pImperativeNestedAction :: Attributes -> ImperativeFlags
>                         -> SV_Parser [ImperativeStatement]
> pImperativeNestedAction atts flags =
>     do pos <- getPos
>        name <- pStartClause SV_KW_action
>        assertEmptyAttributes EAttribsAction atts
>        act <- pImperativeNestedActionStmtsAt flags pos
>        pEndClause SV_KW_endaction name
>        return act

> pImperativeNestedActionStmtsAt :: ImperativeFlags -> Position
>                                -> SV_Parser [ImperativeStatement]
> pImperativeNestedActionStmtsAt flags pos =
>     do let ctxt = stmtContext flags
>        if (ctxt == ISCAction || ctxt == ISCActionValue
>            || ctxt == ISCSequence) then do
>            stmts <- pImperativeStmts (if ctxt == ISCSequence
>                                       then actionFlags else flags)
>            return [ISAction pos stmts]
>         else if allowNakedExpr flags then do
>            e <- pActionsExprAt pos
>            return [ISNakedExpr pos e]
>         else failWithErr (pos, EForbiddenAction (pvpString (stmtContext flags)))

> pImperativeNestedActionValue :: Attributes -> ImperativeFlags
>                              -> SV_Parser [ImperativeStatement]
> pImperativeNestedActionValue atts flags =
>     do pos <- getPos
>        name <- pStartClause SV_KW_actionvalue
>        stmts <- pImperativeNestedActionValueStmtsAt atts flags pos
>        pEndClause SV_KW_endactionvalue name
>        return stmts

> pImperativeNestedActionValueStmtsAt :: Attributes -> ImperativeFlags
>                                     -> Position
>                                     -> SV_Parser [ImperativeStatement]
> pImperativeNestedActionValueStmtsAt atts flags pos =
>     do let ctxt = stmtContext flags
>        if (ctxt == ISCAction || ctxt == ISCActionValue
>            || ctxt == ISCSequence) then do
>            assertEmptyAttributes EAttribsActionValue atts
>            stmts <- pImperativeStmts (if ctxt == ISCSequence
>                                       then actionValueFlags else flags)
>            return [ISActionValue pos stmts]
>         else if allowNakedExpr flags then do
>            assertEmptyAttributes EAttribsActionValue atts
>            e <- pActionValueExpr
>            return [ISNakedExpr pos e]
>         else failWithErr (pos, EForbiddenActionValue (pvpString (stmtContext flags)))

> pImperativeExpression :: SV_Parser CExpr
> pImperativeExpression =
>     do pos <- getPos
>        let flags = expressionFlags
>        block <- pImperativeNestedBeginEnd [] flags
>        imperativeToCExpr pos flags block

> pImperativeTaskCall :: Attributes -> ImperativeFlags -> SV_Parser [ImperativeStatement]
> pImperativeTaskCall atts flags =
>     do pos <- getPos
>        taskName <- pTaskIdentifier <?> "task call"
>        assertEmptyAttributes EAttribsTaskCall atts
>        expr <- pTaskCallPrimaryWith taskName
>        pSemi
>        return [ISNakedExpr pos expr]

> pImperativeDeclOrAssignSemi :: Attributes -> ImperativeFlags
>                             -> SV_Parser [ImperativeStatement]
> pImperativeDeclOrAssignSemi atts flags =
>     do stmts <- pImperativeDeclOrAssign atts flags True
>        pImperativeDeclOrAssignSemi2 flags stmts
>
> pImperativeDeclOrAssignSemi2 :: ImperativeFlags -> [ImperativeStatement]
>                             -> SV_Parser [ImperativeStatement]
> pImperativeDeclOrAssignSemi2 flags stmts =
>     do context <- option [] pProvisos
>        let varName (Right var) = -- single var
>                stringLiteralAt (getIdPosition var) (getIdBaseString var)
>            varName (Left [Right var]) = -- single var
>                stringLiteralAt (getIdPosition var) (getIdBaseString var)
>            varName vars@(Left mis) = -- tuple
>                let pos = getIdOrTuplePosition vars
>                    names = map (either dummyId id) mis
>                    tupleName =
>                        "{" ++
>                        intercalate "," (map getIdBaseString names) ++
>                        "}"
>                in  stringLiteralAt pos tupleName
>            addCtxt (ISDecl pos vars typ []) = ISDecl pos vars typ context
>            addCtxt d =
>                internalError
>                ("CVParser.pImperativeDeclOrAssignSemi.addCtxt: " ++ show d)
>            uninitAssign pos vars =
>                ISEqual pos vars (cVApply (idPrimUninitializedAt pos)
>                                          [posLiteral pos, varName vars])
>            sameVars vs1 vs2 =
>                sort (getIdOrTupleNames vs1) == sort (getIdOrTupleNames vs2)
>            -- avoid initializing declarations that will be immediately
>            -- initialized because it leads to extra variables being created
>            -- and affects variable naming downstream
>            addCtxts [] = []
>            addCtxts (decl@(ISDecl declPos declVars typ [])
>                      : assign@(ISEqual assignPos assignVars expr) : rest)
>                | sameVars assignVars declVars =
>                    addCtxt decl : assign : addCtxts rest
>            addCtxts (decl@(ISDecl declPos declVars typ [])
>                      : assign@(ISBind assignPos pprops assignVars expr) : rest)
>                | sameVars assignVars declVars =
>                    addCtxt decl : assign : addCtxts rest
>            addCtxts (decl@(ISDecl pos vars typ []) : rest)
>                | stmtContext flags == ISCToplevel =
>                    -- don't touch toplevel, because redefining is forbidden
>                    addCtxt decl : addCtxts rest
>                | otherwise =
>                    addCtxt decl : uninitAssign pos vars : addCtxts rest
>            addCtxts (d@(ISDecl _ _ _ _):_) =
>                internalError
>                ("CVParser.pImperativeDeclOrAssignSemi.addCtxt: " ++ show d)
>            addCtxts (stmt:rest) = stmt : addCtxts rest
>        pSemi
>        return (addCtxts stmts)

pImperativDeclOrAssign: parse any statement beginning with a
(optionally qualified) variable or type, e.g.,

  int x;     // allowDecl, allowVariableDecl
  int y = 5; // allowDecl, allowDeclEq
  int x, y, z;
  int x = 5, y = 7;

interesting cases of this;
  1. variable declarations and/or assignment in blocks such as functions, etc.
    a) declaration without assignment is permitted: int x;
    b) declaration with assignment is permitted: int x = 5;
    c) assignment without declaration is permitted: x = 5;
    d) list declaration is permitted: int x[1][3];
    e) comma-separated variables after type declare new variables:
       in "int x, y;" y is a new variable of type int
  2. variable declarations and/or assignment in the init of a for statement
    a) declaration without assignment forbidden (must be =)
    b) declaration with assignment permitted: int x = 5
    c) assignment without declaration is permitted: x = 5
    d) comma-separated variables after type refer to previous variables:
       in "for (int x = 3, y = 5; ...; ...) ..." y refers to a previously
       declared variable
    e) not clear whether list declaration is permitted
  3. variable updates only in the update part of a for statement
    a) declaration forbidden (must use existing variables)
    b) assignment without declaration permitted: x = 5;
    c) increment/decrement/etc operators permitted (+=, ++, etc)

currently, 1a, 1b, 1c, 1d, 2b, 2c, 2d, and 3b are implemented;
also, 2a and 3a are erroneously accepted

> pImperativeDeclOrAssign :: Attributes -> ImperativeFlags -> Bool
>                         -> SV_Parser [ImperativeStatement]
> pImperativeDeclOrAssign atts flags allowManyVarsDecl =
>     do pos <- getPos
>        let noAttrs val = do assertEmptyAttributes EAttribsThisDecl atts
>                             return val
>            noAttrs_ = noAttrs ()
>            (bind_atts, decl_atts) = partition isBindAttrib atts

Note: pVarTypeCases is used twice below; the first time is so as to take
precedence over the naked expression case, and the second is to arrange that
if both fail, the error messages will come from the more likely alternative.

>            pVarTypeCases = (  (pQualIdOrTuple >>=
>                                     pImperativeWithVar decl_atts bind_atts flags pos)
>                              <|>
>                               (pTypeExpr >>= pImperativeWithType decl_atts bind_atts flags))

>        stmt <- (    (pInParens pExpression >>= noAttrs
>                       >>= pImperativeWithExpr decl_atts bind_atts flags pos)
>                 <|> (pKeyword SV_KW_let >>
>                       pImperativeLet decl_atts bind_atts flags pos)
>                 <|> (pKeyword SV_KW_match >> noAttrs_ >>
>                       pImperativePatternDecl flags)
>                 <|> try (do
>                      -- require a match of the whole statement, to avoid parsing just
>                      -- the start of a naked expression that begins with a variable
>                      s <- pVarTypeCases
>                      lookAhead pSemi
>                      return s)
>                 <|> try (do
>                      when (not $ allowNakedExpr flags) (fail "naked expression")
>                      e <- pExpression
>                      -- valid only if it's the whole statement:
>                      lookAhead pSemi
>                      noAttrs_
>                      return (ISNakedExpr pos e))
>                 <|> pVarTypeCases)
>        pImperativeDeclOrAssign2 decl_atts bind_atts flags allowManyVarsDecl stmt


The argument "bind_atts" is a list of attributes for bind (<-) only.
All variables in the decl to which these attributes were passed
must be bound (no mix and match of eq, decl only, bind with the same attrib).

> pImperativeDeclOrAssign2 :: Attributes -> Attributes
>                  -> ImperativeFlags -> Bool
>                  -> ImperativeStatement -> SV_Parser [ImperativeStatement]
> pImperativeDeclOrAssign2 decl_atts bind_atts flags allowManyVarsDecl stmt =
>     do stmts <- pImperativeDeclListOrAssign bind_atts flags stmt
>        case (allowManyVarsDecl, stmts) of
>          (True, ISDecl pos vars typ ps: _) ->
>                  do -- XXX The parse functions should return the base type
>                     -- XXX but since they don't, we reconstruct here.
>                     -- XXX So we have to strip off Array constructors that
>                     -- XXX came from desugaring the bracket syntax, which
>                     -- XXX is not in the base type.
>                     let peelPrimArray (TAp (TCon (TyCon t1 _ _)) t2)
>                             | (t1 == idPrimArray) && (hasIdProp t1 IdPParserGenerated)
>                             = peelPrimArray t2
>                         peelPrimArray t = t
>                         base_ty = fmap peelPrimArray typ
>                     pSymbol SV_SYM_comma
>                     stmts' <- (pCommaSep1
>                                (pImperativeDeclExtraVar decl_atts bind_atts flags base_ty))
>                     return (concat (stmts : stmts'))
>              <|> return stmts
>          _ -> return stmts

> pImperativeDeclListOrAssign :: Attributes
>                             -> ImperativeFlags -> ImperativeStatement
>                             -> SV_Parser [ImperativeStatement]
> pImperativeDeclListOrAssign bind_atts flags stmt@(ISDecl pos vars typ ps) =
>     do let noBindAttrs val =
>                do assertEmptyAttributes EAttribsThisDecl bind_atts
>                   return val
>        (pImperativeDeclListOrAssignNonOptional bind_atts flags stmt
>         <|> (noBindAttrs [stmt]))
> pImperativeDeclListOrAssign bind_atts flags stmt =
>     -- bind_atts are ok for inst and bind, (hopefully) handled previously
>     case stmt of
>         (ISInst {}) -> return [stmt]
>         (ISBind {}) -> return [stmt]
>         (ISUpdateBind {}) -> return [stmt]
>         _ -> do assertEmptyAttributes EAttribsThisDecl bind_atts
>                 return [stmt]

> pImperativeDeclListOrAssignNonOptional :: Attributes -> ImperativeFlags
>      -> ImperativeStatement -> SV_Parser [ImperativeStatement]
> pImperativeDeclListOrAssignNonOptional bind_atts flags stmt@(ISDecl pos vars typ ps) =
>     do let noBindAttrs val =
>                do assertEmptyAttributes EAttribsThisDecl bind_atts
>                   return val
>        (do stmt' <- ((pImperativeWithVarEq flags vars >>= noBindAttrs)
>                      <|> pImperativeWithVarBind bind_atts flags vars
>                      <|> (pImperativeWithVarRegWrite flags pos vars >>=
>                           noBindAttrs))
>            return [stmt, stmt']
>         <|> pImperativeWithVarArrayDecl bind_atts flags vars typ
>         <?> "assignment or subscripting")
> pImperativeDeclListOrAssignNonOptional _ _ _ = internalError "pImperativeDeclListOrAssignNonOptional"

> pImperativeDeclExtraVar :: Attributes -> Attributes
>                         -> ImperativeFlags -> (Maybe CType)
>                         -> SV_Parser [ImperativeStatement]
> pImperativeDeclExtraVar decl_atts bind_atts flags typ =
>     do pos <- getPos
>        var <- pIdentifier
>        keep_attr <- attributes2keep decl_atts
>        -- XXX warn if we're overriding a "keep = 0"?
>        let isKeep = keep_attr || isGlobalKeep
>            var' = if isKeep then setKeepId var else var
>        -- traceM $ "ISDecl (1): \"" ++ pvpString var' ++ "\" (" ++ pvpString typ ++ ")"
>        pImperativeDeclListOrAssign bind_atts flags (ISDecl pos (Right var') typ [])

> pImperativeReturn :: Attributes -> ImperativeFlags
>                   -> SV_Parser [ImperativeStatement]
> pImperativeReturn atts flags =
>     do let ctxt = stmtContext flags
>        pos <- getPos
>        pKeyword SV_KW_return
>        when (not (allowReturn flags))
>                 (failWithErr (pos, EForbiddenReturn
>                               (pvpString (stmtContext flags))))
>        assertEmptyAttributes EAttribsReturn atts
>        expr <- if (ctxt /= ISCSequence) then Just <$> pExpression
>                                         else option Nothing (try $ Just <$> pExpression)
>        pSemi
>        return [ISReturn pos expr]

> data RuleInterior = RRules [([CSchedulePragma],CRule)] | RBody CExpr

> pImperativeRule :: Attributes -> ImperativeFlags
>                 -> SV_Parser [ImperativeStatement]
> pImperativeRule atts flags =
>     do rulePos <- getPos
>        pKeyword SV_KW_rule <?> "rule"
>        when (not (allowRule flags) && stmtContext flags == ISCAction)
>                 (failWithErr (rulePos, EForbiddenRuleInAction))
>        when (not (allowRule flags))
>                 (failWithErr (rulePos, EForbiddenRule
>                               (pvpString (stmtContext flags))))
>        (rprags, sprags) <- attributes2rprags atts
>        namePos <- getPos
>        name <- pIdentifier <?> "rule name"
>        condPos <- getPos
>        let trueCond = [CQFilter (CCon (idTrueAt condPos) [])]
>            errEmptyPredicate =
>                (condPos, EEmptyRulePredicate (pvpString name))
>            pRulePredicate = do
>                option () (pKeyword SV_KW_if)
>                pInParensNonEmpty errEmptyPredicate pCondExpressions
>        conds <- option trueCond pRulePredicate <?> "rule condition"
>        pSemi
>        innards <- ( do prs <- try $ many1 (do as <- pAttributes
>                                               ir <- pImperativeRule as flags
>                                               return $
>                                                 case ir of
>                                                   [ISRule _ _ ps r] -> (ps, r)
>                                                   _ -> internalError "pImperativeRule innards"
>                                           )
>                        return (RRules prs)
>                    <|>
>                     do actionPos <- getPos
>                        body <- pActionsExprAt actionPos
>                        return (RBody body)
>                   )
>        let nameString = getIdString name
>            nameExpr = stringLiteralAt namePos nameString
>            (rule,sprags') = case innards of
>             RBody b   -> (CRule rprags (Just nameExpr) conds b, sprags)
>             RRules psrs ->
>                   let rs = map snd psrs
>                       ps = concat(map fst psrs)
>                   in (CRuleNest  rprags (Just nameExpr) conds rs, ps++sprags)
>        pEndClause SV_KW_endrule (Just name)
>        return [ISRule rulePos name sprags' rule]

> getIfWrapperFromAttribute :: Attributes -> Maybe Id
> getIfWrapperFromAttribute [] = Nothing
> getIfWrapperFromAttribute [(Attribute { attr_name = name,
>                                         attr_value = (AVNum _ 1) })]
>     = Just (case (getIdString name) of
>                      "split" -> idSplitDeepAV
>                      "nosplit" -> idNosplitDeepAV
>                      _ -> error "not 1"
>            )
> getIfWrapperFromAttribute _ = error "not 2"
>

takes a list of Attributes, extracts out the split and nosplit
attributes and returns a list of the remaining.  Checks to make sure
that we don't have things like (* split=0 *) or contradicting (*
split, nosplit *) attributes.  It is permitted to specify it more than
once, e.g. (* split, split *), though it has no extra effect.

> splitInAttributes :: Attributes -> SV_Parser (Maybe Id,Attributes)
> splitInAttributes atts = s' Nothing [] atts
>  where

Both "found" and "accumulator" are accumulating parameters.

>   s' found accumulator atts =
>     case atts of
>       [] -> return (found, reverse accumulator)
>       att@(Attribute { attr_name = name,
>                    attr_value = (AVNum _ num) }):rest
>            | (idname == "split" || idname == "nosplit") && (num /= 1)
>              -> failWithErr ((getPosition att),(ESplitAttributeHasANumberThatIsNotUnity idname num))
>            | (idname == "split" || idname == "nosplit")
>              -> let idid = (case idname of
>                                      "split" -> idSplitDeepAV
>                                      "nosplit" -> idNosplitDeepAV
>                                      _ -> internalError "splitInAttributes"
>                            )
>                 in case found of
>               Nothing -> s' (Just idid) accumulator rest
>               Just prev

this branch indicates that we already found a split/nosplit attribute,
so we need to check that this new one is the same as the old one.

>                         | prev == idid -> s' found accumulator rest
>                         | otherwise -> failWithErr
>                                        ((getPosition att),
>                                         (EConflictingSplitAttributes
>                                          ))
>           where idname = getIdString name
>       att:rest -> s' found (att : accumulator) rest
>

> pImperativeIf :: Attributes -> ImperativeFlags
>               -> SV_Parser [ImperativeStatement]
> pImperativeIf atts flags =
>     do ifPos <- getPos
>        pKeyword SV_KW_if <?> "if-statement"
>        when (not (allowConditionals flags))
>                 (failWithErr (ifPos, EForbiddenIf (pvpString (stmtContext flags))))

attributes (* split *) and (* nosplit *) are eaten by pImperativeStmt
which calls us.

>        assertEmptyAttributes EAttribsIf atts
>        conditions <- pInParens pCondExpressions <?> "if condition"
>        conseqStmts <- pImperativeStmt flags
>        alterStmts <- option Nothing
>                      (fmap Just
>                       (pKeyword SV_KW_else >> pImperativeStmt flags))
>        return [ISIf ifPos conditions conseqStmts alterStmts]

> pImperativeAbtIf :: Attributes -> ImperativeFlags
>               -> SV_Parser [ImperativeStatement]
> pImperativeAbtIf atts flags =
>     do ifPos <- getPos
>        pKeyword SV_KW_abortif <?> "abortif-statement"
>        when (not (allowConditionals flags))
>                 (failWithErr (ifPos, EForbiddenIf (pvpString (stmtContext flags))))
>        assertEmptyAttributes EAttribsIf atts
>        conditions <- pInParens pCondExpressions <?> "abortif condition"
>        conseqStmts <- pImperativeStmt flags
>        alterStmts <- option Nothing
>                      (fmap Just
>                       (pKeyword SV_KW_with >> pImperativeStmt flags))
>        return [ISAbtIf ifPos conditions conseqStmts alterStmts]

> wrapIf :: Id -> CExpr -> CExpr
> wrapIf wrapper inside = CApply (CVar wrapper) [inside]

> pImperativeFor :: Attributes -> ImperativeFlags
>                -> SV_Parser [ImperativeStatement]
> pImperativeFor atts flags =
>     do forPos <- getPos
>        pKeyword SV_KW_for <?> "for-statement"
>        when (not (allowLoops flags)) (failWithErr (forPos, EForbiddenFor (pvpString (stmtContext flags))))
>        assertEmptyAttributes EAttribsFor atts
>        (initStmts, condition, incStmts) <-
>            pInParens (pImperativeForControl flags)
>        body <- pImperativeStmt flags
>        return [ISFor forPos initStmts condition incStmts body]

> pImperativeForControl :: ImperativeFlags
>                       -> SV_Parser ([ImperativeStatement], CExpr,
>                                     [ImperativeStatement])
> pImperativeForControl flags =
>     do let ctxt = stmtContext flags
>            forInitFlags =
>                nullImperativeFlags { allowEq = (ctxt /= ISCSequence),
>                                      allowRegWrite = (ctxt == ISCSequence),
>                                      allowSubscriptAssign = (ctxt == ISCSequence),
>                                      allowFieldAssign = (ctxt == ISCSequence) }
>        initStmtss <-
>            pCommaSep1 (pImperativeDeclOrAssign [] forInitFlags False)
>                           <?> "for-statement initialization"
>        pSemi
>        condition <- pExpression <?> "for-statement condition"
>        pSemi
>        let forIncFlags = forInitFlags
>        incStmtss <- pCommaSep1 (pImperativeDeclOrAssign [] forIncFlags False)
>        return (concat initStmtss, condition, concat incStmtss)

> pImperativeRepeat :: Attributes -> ImperativeFlags
>                  -> SV_Parser [ImperativeStatement]
> pImperativeRepeat atts flags =
>     do repeatPos <- getPos
>        pKeyword SV_KW_repeat <?> "repeat-statement"
>        let ctxt = stmtContext flags
>        when (ctxt /= ISCSequence)
>             (failWithErr (repeatPos, EForbiddenRepeat (pvpString (stmtContext flags))))
>        when (not (allowLoops flags))
>                 (failWithErr (repeatPos, EForbiddenRepeat (pvpString (stmtContext flags))))
>        assertEmptyAttributes EAttribsRepeat atts
>        num <- pInParens pExpression <?> "repeat-statement num"
>        body <- pImperativeStmt flags
>        return [ISRepeat repeatPos num body]

> pImperativeWhile :: Attributes -> ImperativeFlags
>                  -> SV_Parser [ImperativeStatement]
> pImperativeWhile atts flags =
>     do whilePos <- getPos
>        pKeyword SV_KW_while <?> "while-statement"
>        when (not (allowLoops flags))
>                 (failWithErr (whilePos, EForbiddenWhile (pvpString (stmtContext flags))))
>        assertEmptyAttributes EAttribsWhile atts
>        condition <- pInParens pExpression <?> "while-statement condition"
>        body <- pImperativeStmt flags
>        return [ISWhile whilePos condition body]

> pImperativeBreak :: Attributes -> ImperativeFlags
>                  -> SV_Parser [ImperativeStatement]
> pImperativeBreak atts flags =
>     do breakPos <- getPos
>        pKeyword SV_KW_break <?> "break-statement"
>        let ctxt = stmtContext flags
>        when (ctxt /= ISCSequence)
>             (failWithErr (breakPos, EForbiddenBreak (pvpString (stmtContext flags))))
>        when (not (allowLoops flags))
>                 (failWithErr (breakPos, EForbiddenBreak (pvpString (stmtContext flags))))
>        assertEmptyAttributes EAttribsBreak atts
>        pSemi
>        return [ISBreak breakPos]

> pImperativeContinue :: Attributes -> ImperativeFlags
>                  -> SV_Parser [ImperativeStatement]
> pImperativeContinue atts flags =
>     do continuePos <- getPos
>        pKeyword SV_KW_continue <?> "continue-statement"
>        let ctxt = stmtContext flags
>        when (ctxt /= ISCSequence)
>             (failWithErr (continuePos, EForbiddenExpr "continue" (pvpString (stmtContext flags))))
>        when (not (allowLoops flags))
>                 (failWithErr (continuePos, EForbiddenExpr "continue" (pvpString (stmtContext flags))))
>        assertEmptyAttributes (EAttribsExpr "continue") atts
>        pSemi
>        return [ISContinue continuePos]

> pImperativeGoto :: Attributes -> ImperativeFlags
>                  -> SV_Parser [ImperativeStatement]
> pImperativeGoto atts flags =
>     do gotoPos <- getPos
>        pKeyword SV_KW_goto <?> "goto-statement"
>        id <- pIdentifier
>        let ctxt = stmtContext flags
>        when (ctxt /= ISCSequence)
>             (failWithErr (gotoPos, EForbiddenExpr "goto" (pvpString (stmtContext flags))))
>        assertEmptyAttributes (EAttribsExpr "goto") atts
>        pSemi
>        return [ISGoto gotoPos id]

> pImperativeLabel :: Position -> Id -> Attributes -> ImperativeFlags -> SV_Parser [ImperativeStatement]
> pImperativeLabel pos id atts flags =
>  do
>    assertEmptyAttributes (EAttribsExpr "label") atts
>    return [ISLabel pos id]

> pImperativeCase :: Attributes -> ImperativeFlags
>                 -> SV_Parser [ImperativeStatement]
> pImperativeCase atts flags =
>     do casePos <- getPos
>        pKeyword SV_KW_case <?> "case-statement"
>        when (not (allowConditionals flags))
>                 (failWithErr (casePos, EForbiddenCase (pvpString (stmtContext flags))))
>        assertEmptyAttributes EAttribsCase atts
>        subject <- pInParens pExpression
>        (pImperativeCaseMatches casePos flags subject
>         <|> pImperativeCaseIf casePos flags subject)

case statements that turn into ifs (patterns are arbitrary expressions)

> pImperativeCaseIf :: Position -> ImperativeFlags
>                   -> CExpr -> SV_Parser [ImperativeStatement]
> pImperativeCaseIf casePos flags subject =
>     do arms <- many (pImperativeCaseIfArm flags) <?> "case arms"
>        dflt <- option Nothing (pImperativeCaseDefault flags >>=
>                                return . Just)
>        pKeyword SV_KW_endcase
>        return [ISCase casePos subject arms dflt]

> pImperativeCaseIfArm :: ImperativeFlags -> SV_Parser ISCaseArm
> pImperativeCaseIfArm flags =
>            -- XXX "expression" fails badly because of ?: in expressions
>     do pos <- getPos
>        conds <- pCommaSep1 (pPrimaryCaring False)
>        pColon
>        conseqStmts <- pImperativeStmt flags
>        return (pos, conds, conseqStmts)

> pImperativeCaseDefault :: ImperativeFlags
>                        -> SV_Parser ISCaseDefault
> pImperativeCaseDefault flags =
>     do pos <- getPos
>        pKeyword SV_KW_default <?> "case default"
>        option () pColon
>        conseqStmts <- pImperativeStmt flags
>        return (pos, conseqStmts)

pattern-matching case statements

> pImperativeCaseMatches :: Position -> ImperativeFlags
>                        -> CExpr -> SV_Parser [ImperativeStatement]
> pImperativeCaseMatches casePos flags subject =
>     do pKeyword SV_KW_matches <?> "case-matches statement"
>        arms <- many (pImperativeCaseMatchesArm flags)
>        dflt <- option Nothing
>                (Just <$> pImperativeCaseDefault flags)
>        pKeyword SV_KW_endcase
>        return [ISCaseTagged casePos subject arms dflt]

Parse a pattern and return it

> pPattern :: SV_Parser CPat
> pPattern =
>     (pPatternVariable
>      <|> (pKeyword SV_KW_tagged >> pQualConstructor >>= pConstrPatternWith)
>      <|> (pQualConstructor >>= pStructOrEnumPatternWith)
>      <|> pInParens pPattern
>      <|> pTuplePattern
>      <|> pWildcardPattern
>      <|> pConstPattern) <?> "pattern"

> pConstrPatternWith :: Id -> SV_Parser CPat
> pConstrPatternWith constr =
>         do pos <- getPos
>            pInBraces (pConstrFieldsOrTuplePatternWith pos constr)
>     <|> do pat <- (    pWildcardPattern
>                    <|> pConstPattern
>                    <|> pEnumPattern
>                    <|> pInParens pPattern
>                   )
>            return (CPCon constr [pat])
>     <|> do pSymbol SV_SYM_dot
>            var <- pIdentifier
>            return (CPCon constr [CPVar var])
>     <|> return (CPCon constr [])

> pStructOrEnumPatternWith :: Id -> SV_Parser CPat
> pStructOrEnumPatternWith constr =
>         -- XXX require at least one field?
>         (do fields <- pInBraces (pCommaSep pFieldPattern)
>             return (CPstruct (Just True) constr fields))
>     <|> return (CPCon constr [])

> pConstrFieldsOrTuplePatternWith :: Position -> Id -> SV_Parser CPat
> pConstrFieldsOrTuplePatternWith pos constr =
>     -- patterns in tuples can't start with identifiers,
>     -- so these two are ok to combine without 'try'
>         (do pat <- pTuplePatternWith pos
>             return (CPCon constr [pat]))
>     <|> -- use 'pCommaSep' (not 'pCommaSep1'),
>         -- to allow all fields to be omitted
>         (do fields <- pCommaSep pFieldPattern
>             return (CPstruct (Just False) constr fields))

> pPatternVariable :: SV_Parser CPat
> pPatternVariable =
>     do pSymbol SV_SYM_dot
>        name <- pIdentifier
>        return (CPVar name)

> pFieldPattern :: SV_Parser (Id, CPat)
> pFieldPattern =
>     do name <- pIdentifier
>        pat <- ((pColon >> pPattern)
>               ) -- <|> return (CPVar name)) -- JES 26.3.04
>        return (name, pat)

> pNumericLiteralPattern :: SV_Parser CPat
> pNumericLiteralPattern = (pToken accept
>                           <|> (pToken acceptError >>= failWithErr))
>                          <?> "numeric pattern"
>     where accept (SV_Token_Number { start_position = pos,
>                                     value = SV_NUM_Integer num,
>                                     bitwidth = numWidth,
>                                     base = maybeBase }) =
>               let
>                   --  default base to decimal if not specified
>                   numBase = maybe 10 svNumericBaseValue maybeBase
>               in  Just $ CPLit $ CLiteral pos $ LInt $
>                   IntLit {ilWidth = numWidth, ilBase = numBase, ilValue = num}
>           accept (SV_Token_Number { start_position = pos,
>                                     value = SV_NUM_Repeated SV_BIT_0,
>                                     base = maybeBase }) =
>               Just $ CPLit $ CLiteral pos $ LInt $ ilDec 0
>           accept (SV_Token_Number { start_position = pos,
>                                     value = SV_NUM_Mixed bs,
>                                     base = maybeBase })
>            | (all (not . isXZ . snd) bs) =
>               let --  default base to decimal if not specified
>                   numBase = maybe 10 svNumericBaseValue maybeBase
>                   -- convert to CPMixedLit format
>                   mkPair (len, Left num) = (len, Just num)
>                   mkPair (len, Right _) = (len, Nothing)
>               in  Just (CPMixedLit pos numBase (map mkPair bs))
>            where isXZ (Right SV_BIT_X) = True
>                  isXZ (Right SV_BIT_Z) = True
>                  isXZ _ = False
>           accept _ = Nothing
>           acceptError (SV_Token_Number { start_position = pos,
>                                          value = SV_NUM_Repeated _,
>                                          originalText = txt }) =
>               Just (pos, EUnsupportedNumUndetermined txt)
>           acceptError (SV_Token_Number { start_position = pos,
>                                          value = SV_NUM_Mixed _,
>                                          originalText = txt }) =
>               Just (pos, EUnsupportedNumUndetermined txt)
>           acceptError (SV_Token_Number { start_position = pos,
>                                          value = SV_NUM_Real _,
>                                          originalText = txt }) =
>               -- equality of real numbers is tricky, so require users
>               -- to express their meaning of equality via a guard
>               Just (pos, EUnsupportedNumReal txt)
>           acceptError _ = Nothing

> pStringLiteralPattern :: SV_Parser CPat
> pStringLiteralPattern =
>     -- like pStringLiteral, except it returns a pattern
>     do pos <- getPos
>        s   <- pQuotedString <?> "string"
>        return (CPLit $ CLiteral pos $ LString s)

> pConstPattern :: SV_Parser CPat
> pConstPattern =
>         pNumericLiteralPattern                  -- numbers
>     <|> pStringLiteralPattern                   -- strings

> pEnumPattern :: SV_Parser CPat
> pEnumPattern =
>     fmap ((flip CPCon) []) pQualConstructor -- enum-like/void patterns

> pWildcardPattern :: SV_Parser CPat
> pWildcardPattern =
>     do pos <- getPos
>        pSymbol SV_SYM_dot_star
>        return (CPAny pos)

> pTuplePattern :: SV_Parser CPat
> pTuplePattern =
>     do pos <- getPos
>        pInBraces (pTuplePatternWith pos)

> pTuplePatternWith :: Position -> SV_Parser CPat
> pTuplePatternWith pos =
>     -- XXX should we require at least two patterns?
>     fmap (pMkTuple pos) (pCommaSep1 pPattern)

> pImperativeCaseMatchesArm :: ImperativeFlags
>                           -> SV_Parser ISCaseTaggedArm
> pImperativeCaseMatchesArm flags =
>     do pos <- getPos
>        pat <- pPattern <?> "pattern"
>        quals <- option [] (pSymbol SV_SYM_et_et_et >>
>                            fmap (:[]) pPrimary)
>        pColon
>        conseqStmts <- pImperativeStmt flags
>        return (pos, pat, quals, conseqStmts)

> pDefaultClockWith :: (Maybe Id) -> SV_Parser [ImperativeStatement]
> pDefaultClockWith mid =
>     do pos <- getPos
>        ( (do pSemi
>              when (isNothing mid) (fail "default_clock statement arguments")
>              return [ISBVI pos (BVI_default_clock (fromJust mid))])
>         <|>
>          (do let defci id = (id, Just (V.VName "CLK", Right (V.VName "CLK_GATE")))
>                  defexp = (CVar idExposeCurrentClock, True)
>              ci <- option defci (pInputClockInfAwaitingId)
>              (e,b) <- option defexp pVExpr
>              pSemi
>              let id = case (mid,e,b) of
>                         (Just i, _, _) -> i
>                         (Nothing, CVar i, False) -> i
>                         _ -> -- use an empty name ("") and we'll fix it later
>                              -- when we have all the clock names (position is
>                              -- used to distinguish multiple empty names)
>                              setIdPosition pos emptyId
>              return ([ISBVI pos (BVI_default_clock id),
>                       ISBVI pos (BVI_input_clock (ci id)),
>                       ISBVI pos (BVI_arg (V.ClockArg id, e, b))])))

> pDefaultResetWith :: (Maybe Id) -> SV_Parser [ImperativeStatement]
> pDefaultResetWith mid =
>     do pos <- getPos
>        ( (do pSemi
>              when (isNothing mid) (fail "default_reset statement arguments")
>              return [ISBVI pos (BVI_default_reset (fromJust mid))])
>         <|>
>          (do let defri id = (id, (Nothing, Nothing))
>                  defexp = (CVar idExposeCurrentReset, True)
>              ri <- option defri (pResetInfAwaitingId)
>              (e,b) <- option defexp pVExpr
>              pSemi
>              let id = case (mid,e,b) of
>                         (Just i, _, _) -> i
>                         (Nothing, CVar i, False) -> i
>                         _ -> -- use an empty name ("") and we'll fix it later
>                              -- when we have all the reset names (position is
>                              -- used to distinguish multiple empty names)
>                              setIdPosition pos emptyId
>              return ([ISBVI pos (BVI_default_reset id),
>                       ISBVI pos (BVI_input_reset (ri id)),
>                       ISBVI pos (BVI_arg (V.ResetArg id, e, b))])))

> pImperativeBVI :: Attributes -> ImperativeFlags
>                -> SV_Parser [ImperativeStatement]
> pImperativeBVI atts flags =
>     do pos <- getPos
>        when (stmtContext flags /= ISCBVI) (fail "imperative statement (not BVI context)")
>        res <- (
>         (do pTheString "default_clock"
>             mid <- option Nothing (fmap Just pDottedName)
>             pDefaultClockWith mid)
>         <|>
>         (do pTheString "default_reset"
>             mid <- option Nothing (fmap Just pDottedName)
>             pDefaultResetWith mid)
>         <|>
>         (do pTheString "no_reset"
>             pSemi
>             let no_reset_id = mkId pos (mkFString "no_reset")
>             return [ISBVI pos (BVI_default_reset no_reset_id)])
>         <|>
>         (do pTheString "input_clock"
>             mid <- option Nothing (fmap Just pIdentifier)
>             ci <- pInputClockInfAwaitingId
>             (e,b) <- pVExpr
>             pSemi
>             let id = case (mid,e,b) of
>                  (Just i, _, _) -> i
>                  (Nothing, CVar i, False) -> i
>                  _ -> -- use an empty name ("") and we'll fix it later
>                       -- when we have all the clock names (position is
>                       -- used to distinguish multiple empty names)
>                       setIdPosition pos emptyId
>                 cinf = ci id
>                 (_, mps) = cinf
>             when (isNothing mps && isNothing mid)
>                  (fail "input_clock (must have connections or name)")
>             return [ISBVI pos (BVI_input_clock cinf),
>                     ISBVI pos (BVI_arg (V.ClockArg id, e, b))])
>         <|>
>         (do pTheString "input_reset"
>             mid <- option Nothing (fmap Just pIdentifier)
>             ri <- pResetInfAwaitingId
>             (e,b) <- pVExpr
>             pSemi
>             let id = case (mid,e,b) of
>                  (Just i, _, _) -> i
>                  (Nothing, CVar i, False) -> i
>                  _ -> -- use an empty name ("") and we'll fix it later
>                       -- when we have all the reset names (position is
>                       -- used to distinguish multiple empty names)
>                       setIdPosition pos emptyId
>                 rinf = ri id
>                 (_, (mp,_)) = rinf
>             when (isNothing mp && isNothing mid)
>                  (fail "input_reset (must have port or name)")
>             return [ISBVI pos (BVI_input_reset rinf),
>                     ISBVI pos (BVI_arg (V.ResetArg id, e, b))])
>         <|>
>         (do pKeyword SV_KW_inout
>             vname <- pVName
>             (mclk, mrst) <- pVArgPortOptions
>             (e,b) <- pVExpr
>             pSemi
>             return [ISBVI pos (BVI_arg (V.InoutArg vname mclk mrst, e, b))])
>         <|>
>         (do pTheString "ancestor"
>             p <- pVClockPair
>             return [ISBVI pos (BVI_ancestor p)])
>         <|>
>         (do pTheString "same_family"
>             p <- pVClockPair
>             return [ISBVI pos (BVI_family p)])
>         <|>
>         (do pKeyword SV_KW_parameter
>             a <- pVArgParam
>             return [ISBVI pos (BVI_arg a)])
>         <|>
>         (do pTheString "port"
>             a <- pVArgPort
>             return [ISBVI pos (BVI_arg a)])
>         <|>
>         (do pTheString "schedule"
>             s <- pVMethodConflict
>             return [ISBVI pos (BVI_schedule s)])
>         <|>
>         (do pTheString "path"
>             p <- pVPath
>             return [ISBVI pos (BVI_path p)])
>         <|>
>         (do pTheString "unsync"
>             ms <- pCommaSep pIdentifier
>             pSemi
>             return [ISBVI pos (BVI_unsync ms)])
>         <|>
>         pBVINested emptyId
>         <?> "imperative BVI statement")
>        assertEmptyAttributes EAttribsBVI atts
>        return res

Parser for the BVI statements which may be nested inside "interface"
statements: interface, method, output_clock, output_reset

> pBVINested :: Id -> SV_Parser [ImperativeStatement]
> pBVINested  prefix =
>     do pos <- getPos
>        ((do pKeyword SV_KW_method
>             ms <- pMethodVeriProt prefix
>             return (map (\ mb -> ISBVI pos (BVI_method mb)) ms))
>         <|>
>         (do pTheString "output_clock"
>             id <- pIdentifier
>             ci <- pOutputClockInfAwaitingId
>             pSemi
>             let prefixedId = mkUSId prefix id
>             return [ISBVI pos (BVI_output_clock (ci prefixedId)),
>                     ISBVI pos (BVI_method (id,V.Clock prefixedId,False))])
>         <|>
>         (do pTheString "output_reset"
>             id <- pIdentifier
>             ci <- pResetInfAwaitingId
>             pSemi
>             let prefixedId = mkUSId prefix id
>             return [ISBVI pos (BVI_output_reset (ci prefixedId)),
>                     ISBVI pos (BVI_method (id,V.Reset prefixedId,False))])
>         <|>
>         (do pTheString "ifc_inout"
>             id <- pIdentifier
>             vname <- pInParens (pVName)
>             (mclk, mrst) <- pVArgPortOptions
>             pSemi
>             let prefixedId = mkUSId prefix id
>                 vfi = V.Inout prefixedId vname mclk mrst
>             return [ISBVI pos (BVI_method (id,vfi,False))])
>         <|>
>         (do pKeyword SV_KW_interface
>             constr <- pQualConstructor <?> "subinterface type constructor"
>             name <- pIdentifier <?> "subinterface name"
>             pSemi
>             ims <- fmap concat (many1 (pBVINested (mkUSId prefix name)))
>             pEndClause SV_KW_endinterface (Just name)
>             return [ISBVI pos (BVI_interface (name, constr, ims))])
>         <?> "imperative BVI statement")

> pInputClockInfAwaitingId :: SV_Parser (Id -> V.InputClockInf)
> pInputClockInfAwaitingId  =
>   let pInputGateProp = do
>           pos <- getPos
>           propString <- pWord <?> "property"
>           case propString of
>               "inhigh" -> return True
>               "unused" -> return False
>               _ -> let loc = "an input clock gate"
>                        allowed = ["inhigh", "unused"]
>                    in  failWithErr
>                            (pos, EBadPortProperty loc propString allowed)
>       pInputGateProps = do
>           pSymbol SV_SYM_lparen_star
>           -- only one prop allowed, better error?
>           p <- pInputGateProp
>           pSymbol SV_SYM_star_rparen
>           return p
>       pInputGateWire = do
>           mprop <- option Nothing (Just <$> pInputGateProps)
>           vn_gate <- pVName
>           case mprop of
>               Nothing -> return (Right vn_gate)
>               Just p  -> return (Left p)
>       pInputClockWires = do
>           vp_osc <- pVName
>           vp_gate <- option (Left True) (do pSymbol SV_SYM_comma
>                                             pInputGateWire)
>           return (\i -> (i, Just (vp_osc, vp_gate)))
>       defaultInputClockInf = (\i -> (i, Nothing))
>   in  pInParens (option defaultInputClockInf pInputClockWires)

> pOutputClockInfAwaitingId :: SV_Parser (Id -> V.OutputClockInf)
> pOutputClockInfAwaitingId  =
>   let pOutputGateProp = do
>           pos <- getPos
>           propString <- pWord <?> "property"
>           case propString of
>               "outhigh" -> return V.VPouthigh
>               _ -> let loc = "an output clock gate"
>                        allowed = ["outhigh"]
>                    in  failWithErr
>                            (pos, EBadPortProperty loc propString allowed)
>       pOutputGateProps = do
>           pSymbol SV_SYM_lparen_star
>           p <- pOutputGateProp
>           pSymbol SV_SYM_star_rparen
>           -- only one prop allowed, better error?
>           return [p]
>       pOutputGateWire = do
>           props <- option [] pOutputGateProps
>           vn_gate <- pVName
>           return (Just (vn_gate, props))
>       pOutputClockWires = do
>           vp_osc <- pVName
>           vp_gate <- option Nothing (do pSymbol SV_SYM_comma
>                                         pOutputGateWire)
>           return (\i -> (i, Just (vp_osc, vp_gate)))
>       defaultOutputClockInf = (\i -> (i, Nothing))
>   in  pInParens (option defaultOutputClockInf pOutputClockWires)

> pResetInfAwaitingId :: SV_Parser (Id -> V.ResetInf)
> pResetInfAwaitingId =
>     do pos <- getPos
>        ps <- pInParens (pCommaSep pVName)
>        mc <- option Nothing (do pKeyword SV_KW_clocked_by
>                                 n <- pInParens pDottedName
>                                 return (Just n))
>        case ps of
>           []  -> return (\ i -> (i, (Nothing,mc)))
>           [p] -> return (\ i -> (i, (Just p, mc)))
>           _ -> failWithErr (pos, EInvalidNoOfResetPorts)

METHODS

function/method name, return type optional

> pFunctionNameOptType :: SV_Parser (Maybe CType, Id)
> pFunctionNameOptType =
>     (do anId <- pIdentifier
>         ((do rettype <- pTypeExprWith (cTVar anId)
>              rettype' <- pOptArrayDimensions rettype
>              name <- pIdentifier <?> "function name"
>              return (Just rettype', name))
>          <|>
>          (return (Nothing, anId))))
>     <|>
>     (do rettype <- pTypeExpr
>         rettype' <- pOptArrayDimensions rettype
>         name <- pIdentifier <?> "function name"
>         return (Just rettype', name)) <?> "function name or type"

The same, but reads an output port name instead of a type

> pMethodNameOptOPort :: SV_Parser (Maybe V.VPort, Id)
> pMethodNameOptOPort =
>     (do pos <- getPos
>         aPort <- pMethodValVeriPort -- might be output port, or method name (wrongly packed)
>         let anId = case aPort of
>                      (V.VName i, _) -> mk_dangling_id i pos
>         ((do name <- pIdentifier <?> "method name"
>              return (Just aPort, name))
>          <|>
>          (return (Nothing, anId))))

> pImperativeMethod :: Attributes -> ImperativeFlags
>                   -> SV_Parser [ImperativeStatement]
> pImperativeMethod atts flags =
>     do pos <- getPos
>        pKeyword SV_KW_method <?> "method"
>        when (not (allowMethod flags))
>                 (failWithErr
>                  (pos, EForbiddenMethod (pvpString (stmtContext flags))))
>        assertEmptyAttributes EAttribsMethod atts
>        (maybeRetType, name) <- pFunctionNameOptType
>                                <?> "method return type or name"
>        args <- option [] (pInParens (pCommaSep pFunctionArgOptType))
>                <?> "method arguments"
>        let (argTypeMaybes, argIds) = unzip args
>            duplicateArgs = [(arg1, arg2)
>                             | (arg1:arg2:_) <- group $ sort $ argIds]
>        when (not (null duplicateArgs))
>                 (let (arg1, arg2) = head duplicateArgs
>                  in  failWithErr (getIdPosition arg2,
>                                   (EDuplicateMethodArg (pvpString name)
>                                    (pvpString arg1) (getIdPosition arg1))))
>        context <- option [] pProvisos
>        conditions <- option []
>                      (pKeyword SV_KW_if >> pInParens pCondExpressions)
>                      <?> "method condition"
>        let isAction = maybeRetType == Just tAction
>            isActionValue =
>                maybe False (\t -> leftCon t == Just idActionValue)
>                      maybeRetType
>        body <- (do pSemi
>                    expr <- pFunctionBody pos name args FTMethod
>                            (isAction, isActionValue)
>                    pEndClause SV_KW_endmethod (Just name)
>                    return expr)
>                <|>
>                (do pEq
>                    expr <- pExpression
>                    pSemi
>                    return expr)
>        -- return type and argument types may be omitted
>        -- if enough type information is provided, generate
>        -- a signed definition; otherwise an unsigned definition
>        let bodyClause = CClause (map CPVar argIds) [] body
>            maybeTypes = sequence (maybeRetType:argTypeMaybes)
>        def <- case maybeTypes of
>                  Just (retType:argTypes) ->
>                      let methType =
>                                  CQType context (foldr fn retType argTypes)
>                          def = CDef name methType [bodyClause]
>                      in  return $ CLValueSign def conditions
>                  Nothing -> do
>                      let hasArgType = any isJust argTypeMaybes
>                          hasRetType = (isJust maybeRetType) && (not isAction)
>                      when (hasArgType || hasRetType) $
>                          parseWarn (pos, WTypesIgnored "method")
>                      return $ CLValue name [bodyClause] conditions
>                  Just [] -> internalError ("CVParser.imperativeMethod.def: "
>                                            ++ "sequence returned Just []")
>        return [ISMethod pos def]

> pImperativeFunction :: Attributes -> ImperativeFlags
>                     -> SV_Parser [ImperativeStatement]
> pImperativeFunction atts flags =
>     do pos <- getPos
>        pKeyword SV_KW_function <?> "function definition"
>        when (not (allowFunction flags))
>             (failWithErr
>              (pos, EForbiddenFunction (pvpString (stmtContext flags))))
>        when (stmtContext flags /= ISCToplevel)
>             (assertEmptyAttributes EAttribsLocalFunction atts)
>        def <- pFunctionAfterKeyword pos
>        pragmas <- attributes2funcpragma (getLName def) atts
>        return [ISFunction pos pragmas def]

> pImperativeWithVarEq :: ImperativeFlags -> IdOrTuple
>                      -> SV_Parser ImperativeStatement
> pImperativeWithVarEq flags vars =
>     do pos <- getPos
>        pEq
>        when (not (allowEq flags))
>                 (failWithErr
>                  (pos, EBadAssignEq (pvpString (stmtContext flags))))
>        fmap (ISEqual pos vars) pExpression

> pImperativeWithExprEq :: ImperativeFlags -> Position -> CExpr
>                      -> SV_Parser ImperativeStatement
> pImperativeWithExprEq flags pos expr =
>     do pEq
>        when (not (allowEq flags))
>                 (failWithErr
>                  (pos, EBadAssignEq (pvpString (stmtContext flags))))
>        fmap (ISUpdate pos expr) pExpression

> pImperativeWithVarBind :: Attributes -> ImperativeFlags -> IdOrTuple
>                        -> SV_Parser ImperativeStatement
> pImperativeWithVarBind bind_atts flags vars =
>     do pos <- getPos
>        pSymbol SV_SYM_lt_minus
>        when (not (allowBind flags))
>                 (failWithErr
>                  (pos, EBadAssignBind (pvpString (stmtContext flags))))
>        -- allow bind attributes if we're on a module monad and binding only one thing
>        bindprops
>            <- case (isModuleContext (stmtContext flags), vars) of
>                 (True, Right _) -> attributes2instpprops bind_atts
>                 (True, Left [Right _]) -> attributes2instpprops bind_atts
>                 _ -> do assertEmptyAttributes EAttribsThisDecl bind_atts
>                         return []
>        fmap (ISBind pos bindprops vars) pExpression

> pImperativeWithExprBind :: Attributes -> ImperativeFlags -> Position -> CExpr
>                        -> SV_Parser ImperativeStatement
> pImperativeWithExprBind bind_atts flags pos expr =
>     do pSymbol SV_SYM_lt_minus
>        when (not (allowBind flags))
>                 (failWithErr
>                  (pos, EBadAssignBind (pvpString (stmtContext flags))))
>        bindprops
>            <- if (isModuleContext (stmtContext flags))
>               then attributes2instpprops bind_atts
>               else do assertEmptyAttributes EAttribsThisDecl bind_atts
>                       return []
>        fmap (ISUpdateBind pos bindprops expr) pExpression


> pArrayInitialize :: [(CExpr, Position)] -> SV_Parser (CExpr, Position)
> pArrayInitialize [] = fail "array dimension lost"
> pArrayInitialize ((dim, decpos):[]) =
>     do
>        -- the position of the init expression, for errors on the expr
>        pos <- getPos
>        -- pExpPos returns the position of the comma/brace after each expr,
>        -- for giving a position to the "cons"
>        exp_pos <- (do expPoses <- pInBraces (pCommaSep1 pExpPos) <?> "array initialization"
>                       let ccons (e,p) (es,_) = (CCon (idCons p) [e, es], p)
>                           cnil  = (CCon (idNil decpos) [], decpos)
>                           (ex, _) = foldr ccons cnil expPoses
>                           arrinit = cVApply (idPrimArrayInitializeAt decpos) [ex]
>                           arrchk = cVApply (idPrimArrayCheckAt decpos) [posLiteral pos, dim, arrinit]
>                       return (arrchk, decpos))
>                    <|>
>                   (do (expr, cpos) <- pExpPos
>                       let arrchk = cVApply (idPrimArrayCheckAt decpos) [posLiteral pos, dim, expr]
>                       return (arrchk, cpos))
>
>        return exp_pos
> pArrayInitialize ((dim, decpos):rest) =
>     do
>        -- the position of the init expression, for errors on the expr
>        pos <- getPos
>        -- pExpPos returns the position of the comma/brace after each expr,
>        -- for giving a position to the "cons"
>        exp_pos <- (do expPoses <- pInBraces (pCommaSep1 (pArrayInitialize rest)) <?> "multi-dimensional array initialization"
>                       let ccons (e,p) (es,_) = (CCon (idCons p) [e, es], p)
>                           cnil  = (CCon (idNil decpos) [], decpos)
>                           (ex, _) = foldr ccons cnil expPoses
>                           arrinit = cVApply (idPrimArrayInitializeAt decpos) [ex]
>                           arrchk = cVApply (idPrimArrayCheckAt decpos) [posLiteral pos, dim, arrinit]
>                       return (arrchk, decpos))
>                    <|>
>                   (do (expr, cpos) <- pExpPos
>                       -- XXX this doesn't check the size of the inner arrays
>                       let arrchk = cVApply (idPrimArrayCheckAt decpos) [posLiteral pos, dim, expr]
>                       return (arrchk, cpos))
>        return exp_pos


> -- this returns the position *of* the expression
> pPosExp :: SV_Parser (CExpr, Position)
> pPosExp =
>     do p <- getPos
>        e <- pExpression
>        return (e,p)


> pImperativeWithVarArrayDecl :: Attributes -> ImperativeFlags -> IdOrTuple -> Maybe CType
>                            -> SV_Parser [ImperativeStatement]
> pImperativeWithVarArrayDecl bind_atts flags (Right var) maybe_typ =
>     do pos <- getPos
>        -- Parse the dimensions
>        -- use pPosExp so that the position is the position *of* the dim
>        dimensions <- many1 (pInBrackets pPosExp)
>        -- Construct the array type (by number of dimensions)
>        typ <- case (maybe_typ) of
>                 Nothing -> do pos <- getPos
>                               failWithErr (pos, ETypesRequired (pvpString var))
>                 Just t -> return t
>        let mkArrayType (_, pos) typ =
>                -- mark the PrimArray constructor so that it can be peeled off
>                -- to reconstruct the base type (for multiple var decls)
>                let arr_con_id = addIdProp (idPrimArrayAt pos) IdPParserGenerated
>                in  cTApplys (cTCon arr_con_id) [typ]
>            arrayType = Just (foldr mkArrayType typ dimensions)
>        -- Construct an uninitialized value (if the variable is not assigned)
>        let -- XXX uninitialized error message shows only innermost dimension
>            mkArrayInit [] = internalError
>                            "imperativeWithVarArrayDecl: no dimensions"
>            mkArrayInit [(dim, pos)] = cVApply (idPrimArrayNewUAt pos) [dim]
>            mkArrayInit ((dim, pos):rest) = cVApply (idPrimArrayNewAt pos) [dim, innerArray]
>                where innerArray = mkArrayInit rest
>            arrayInit = mkArrayInit dimensions
>        -- Parse for eq-assignment, bind, or uninitialized
>        let parse_eq =
>                do pEq
>                   (expr, _) <- pArrayInitialize dimensions
>                   assertEmptyAttributes EAttribsThisDecl bind_atts
>                   return $ ISEqual pos (Right var) expr
>        let parse_bind =
>                do pSymbol SV_SYM_lt_minus
>                   when (not (allowBind flags)) $
>                       failWithErr
>                         (pos, EBadAssignBind (pvpString (stmtContext flags)))
>                   bindprops
>                       <- if (isModuleContext (stmtContext flags))
>                          then attributes2instpprops bind_atts
>                          else do assertEmptyAttributes EAttribsThisDecl bind_atts
>                                  return []
>                   -- code taken from pArrayInitialize
>                   (expr, e_pos) <- pExpPos
>                   dim <- case dimensions of
>                            ((v,_):_) -> return v
>                            _ -> fail "array dimension lost"
>                   -- XXX this doesn't check the size of the inner arrays
>                   let arrchk = cVApply idFmap $
>                                  [cVApply (idPrimArrayCheckAt pos) [posLiteral e_pos, dim],
>                                   expr]
>                   return $ ISBind pos bindprops (Right var) arrchk
>        let parse_uninit =
>                do assertEmptyAttributes EAttribsThisDecl bind_atts
>                   return $ ISEqual pos (Right var) arrayInit
>        assign_stmt <- parse_eq <|> parse_bind <|> parse_uninit
>        -- Return a declaration and an assignment
>        return [ISDecl (getIdPosition var) (Right var) arrayType [],
>                assign_stmt]
>
> pImperativeWithVarArrayDecl _ _ _ _ =
>     do pos <- getPos
>        failWithErr (pos, EForbiddenTuple)


> pImperativeWithExprRegWrite :: ImperativeFlags -> Position -> CExpr
>                             -> SV_Parser ImperativeStatement
> pImperativeWithExprRegWrite flags _ regExpr =
>     do pos <- getPos
>        pSymbol SV_SYM_lt_eq
>        let missingHint | stmtContext flags /= ISCExpression = Nothing
>                        | otherwise = Just "action ... endaction"
>        when (not (allowRegWrite flags))
>                 (failWithErr (pos, EBadAssignRegWrite
>                               (pvpString (stmtContext flags)) missingHint))
>        fmap (ISRegWrite pos regExpr) pExpression

> pImperativeWithVarRegWrite :: ImperativeFlags -> Position -> IdOrTuple
>                            -> SV_Parser ImperativeStatement
> pImperativeWithVarRegWrite flags pos (Right var) =
>     pImperativeWithExprRegWrite flags pos (cVar var)
> pImperativeWithVarRegWrite flags pos vars =
>     failWithErr (pos, EForbiddenTuple)

> pImperativeWithVarDecl :: Attributes -> Attributes -> ImperativeFlags -> IdOrTuple
>                        -> SV_Parser ImperativeStatement
> pImperativeWithVarDecl decl_atts bind_atts flags (Right var) =
>     pTypeExprWith (cTVar var) >>=
>     pImperativeWithType decl_atts bind_atts flags
> pImperativeWithVarDecl decl_atts bind_atts flags vars =
>     failWithErr (getIdOrTuplePosition vars, EForbiddenTuple)

> pImperativeWithExprNakedExpr :: ImperativeFlags -> Position -> CExpr
>                              -> SV_Parser ImperativeStatement
> pImperativeWithExprNakedExpr flags exprPos expr =
>     do
>        when (allowAssertVar flags) (fail "Sequence") --let the sequence parser take over
>        when (not (allowNakedExpr flags)
>              && stmtContext flags == ISCExpression)
>                 (failWithErr (exprPos, EForbiddenNakedExprInExprBlock))
>        when (not (allowNakedExpr flags))
>                 (failWithErr (exprPos, EForbiddenNakedExpr
>                               (pvpString (stmtContext flags))))
>        return (ISNakedExpr exprPos expr)

> pImperativeWithVarCall :: Attributes -> ImperativeFlags -> IdOrTuple
>                        -> SV_Parser ImperativeStatement
> pImperativeWithVarCall bind_atts flags (Right var) =
>   let noBindAttrs val = do assertEmptyAttributes EAttribsThisDecl bind_atts
>                            return val
>   in
>     do pos <- getPos
>        primy <- pPrimaryWithSuffix (cVar var)
>        ((pImperativeWithCallRegWrite flags pos primy >>= noBindAttrs)
>         <|> (pImperativeWithCallEq flags primy >>= noBindAttrs)
>         <|> pImperativeWithCallBind bind_atts flags primy
>         -- Naked expressions are accepted here, so that a helpful error
>         -- for that situation can be given (EForbiddenNakedExprInExprBlock).
>         <|> (pImperativeWithExprNakedExpr flags pos primy >>= noBindAttrs))
> pImperativeWithVarCall bind_attrs flags vars =
>     failWithErr (getIdOrTuplePosition vars, EForbiddenTuple)

> pImperativeWithExprCall :: ImperativeFlags -> Position -> CExpr
>                         -> SV_Parser ImperativeStatement
> pImperativeWithExprCall flags pos expr =
>     do primy <- pPrimaryWithSuffix expr
>        (pImperativeWithExprRegWrite flags pos primy
>         <|> pImperativeWithExprNakedExpr flags pos primy)

> pImperativeWithCallEq :: ImperativeFlags -> CExpr
>                       -> SV_Parser ImperativeStatement
> pImperativeWithCallEq flags expr@(CSelect _ _) =
>     do pos <- getPos
>        pEq
>        when (not (allowEq flags))
>                 (failWithErr
>                  (pos, EBadAssignEq (pvpString (stmtContext flags))))
>        when (not (allowFieldAssign flags))
>                 (failWithErr
>                  (pos, EBadAssignField (pvpString (stmtContext flags))))
>        fmap (ISUpdate pos expr) pExpression
> pImperativeWithCallEq flags expr@(CSub _ _ _) =
>     do pos <- getPos
>        pEq
>        when (not (allowEq flags))
>                 (failWithErr
>                  (pos, EBadAssignEq (pvpString (stmtContext flags))))
>        when (not (allowSubscriptAssign flags))
>                 (failWithErr
>                  (pos, EBadAssignSubscript (pvpString (stmtContext flags))))
>        fmap (ISUpdate pos expr) pExpression
> pImperativeWithCallEq flags expr@(CSub2 _ _ _) =
>     do pos <- getPos
>        pEq
>        when (not (allowEq flags))
>                 (failWithErr
>                  (pos, EBadAssignEq (pvpString (stmtContext flags))))
>        when (not (allowSubscriptAssign flags))
>                 (failWithErr
>                  (pos, EBadAssignSubscript (pvpString (stmtContext flags))))
>        fmap (ISUpdate pos expr) pExpression
> pImperativeWithCallEq flags _ =
>     do pos <- getPos
>        pEq
>        when (not (allowEq flags))
>                 (failWithErr
>                  (pos, EBadAssignEq (pvpString (stmtContext flags))))
>        failWithErr (pos, EBadLValue)

> pImperativeWithCallRegWrite :: ImperativeFlags -> Position -> CExpr
>                             -> SV_Parser ImperativeStatement
> pImperativeWithCallRegWrite flags pos expr@(CSelect _ _) =
>     do pSymbol SV_SYM_lt_eq
>        let missingHint | stmtContext flags /= ISCExpression = Nothing
>                        | otherwise = Just "action ... endaction"
>        when (not (allowRegWrite flags))
>                 (failWithErr
>                  (pos, EBadAssignRegWrite (pvpString (stmtContext flags))
>                   missingHint))
>        when (not (allowFieldAssign flags))
>                 (failWithErr
>                  (pos, EBadAssignField (pvpString (stmtContext flags))))
>        fmap (ISUpdateReg pos expr) pExpression
> pImperativeWithCallRegWrite flags pos expr@(CSub _ _ _) =
>     do pSymbol SV_SYM_lt_eq
>        let missingHint | stmtContext flags /= ISCExpression = Nothing
>                        | otherwise = Just "action ... endaction"
>        when (not (allowRegWrite flags))
>                 (failWithErr
>                  (pos, EBadAssignRegWrite (pvpString (stmtContext flags))
>                   missingHint))
>        when (not (allowSubscriptAssign flags))
>                 (failWithErr
>                  (pos, EBadAssignSubscript (pvpString (stmtContext flags))))
>        fmap (ISUpdateReg pos expr) pExpression
> pImperativeWithCallRegWrite flags pos expr@(CSub2 _ _ _) =
>     do pSymbol SV_SYM_lt_eq
>        let missingHint | stmtContext flags /= ISCExpression = Nothing
>                        | otherwise = Just "action ... endaction"
>        when (not (allowRegWrite flags))
>                 (failWithErr
>                  (pos, EBadAssignRegWrite (pvpString (stmtContext flags))
>                   missingHint))
>        when (not (allowSubscriptAssign flags))
>                 (failWithErr
>                  (pos, EBadAssignSubscript (pvpString (stmtContext flags))))
>        fmap (ISUpdateReg pos expr) pExpression
> pImperativeWithCallRegWrite flags pos expr =
>     pImperativeWithExprRegWrite flags pos expr

> pImperativeWithCallBind :: Attributes -> ImperativeFlags -> CExpr
>                         -> SV_Parser ImperativeStatement
> pImperativeWithCallBind bind_atts flags expr@(CSelect _ _) =
>     do pos <- getPos
>        pSymbol SV_SYM_lt_minus
>        when (not (allowBind flags))
>                 (failWithErr
>                  (pos, EBadAssignBind (pvpString (stmtContext flags))))
>        when (not (allowFieldAssign flags))
>                 (failWithErr
>                  (pos, EBadAssignField (pvpString (stmtContext flags))))
>        bindprops
>            <- if (isModuleContext (stmtContext flags))
>               then attributes2instpprops bind_atts
>               else do assertEmptyAttributes EAttribsThisDecl bind_atts
>                       return []
>        fmap (ISUpdateBind pos bindprops expr) pExpression
> pImperativeWithCallBind bind_atts flags expr@(CSub _ _ _) =
>     do pos <- getPos
>        pSymbol SV_SYM_lt_minus
>        when (not (allowBind flags))
>                 (failWithErr
>                  (pos, EBadAssignBind (pvpString (stmtContext flags))))
>        when (not (allowSubscriptAssign flags))
>                 (failWithErr
>                  (pos, EBadAssignSubscript (pvpString (stmtContext flags))))
>        bindprops
>            <- if (isModuleContext (stmtContext flags))
>               then attributes2instpprops bind_atts
>               else do assertEmptyAttributes EAttribsThisDecl bind_atts
>                       return []
>        fmap (ISUpdateBind pos bindprops expr) pExpression
> pImperativeWithCallBind bind_atts flags expr@(CSub2 _ _ _) =
>     do pos <- getPos
>        pSymbol SV_SYM_lt_minus
>        when (not (allowBind flags))
>                 (failWithErr
>                  (pos, EBadAssignBind (pvpString (stmtContext flags))))
>        when (not (allowSubscriptAssign flags))
>                 (failWithErr
>                  (pos, EBadAssignSubscript (pvpString (stmtContext flags))))
>        bindprops
>            <- if (isModuleContext (stmtContext flags))
>               then attributes2instpprops bind_atts
>               else do assertEmptyAttributes EAttribsThisDecl bind_atts
>                       return []
>        fmap (ISUpdateBind pos bindprops expr) pExpression
> pImperativeWithCallBind _ flags _ =
>     do pos <- getPos
>        pSymbol SV_SYM_lt_minus
>        when (not (allowBind flags))
>                 (failWithErr
>                  (pos, EBadAssignBind (pvpString (stmtContext flags))))
>        failWithErr (pos, EBadLValue)

> pImperativeWithType :: Attributes -> Attributes -> ImperativeFlags -> CType
>                     -> SV_Parser ImperativeStatement
> pImperativeWithType decl_atts bind_atts flags typ =
>     do pos <- getPos
>        vars <- pIdOrTuple
>        case (vars) of
>          Right i -> (pImperativeWithTypeAndVarInst bind_atts flags (Just typ) i)
>                     <|> doDefault pos vars
>          Left _ -> doDefault pos vars
>  where
>    doDefault pos vars =
>         do keep_attr <- attributes2keep decl_atts
>            -- XXX warn if we're overriding a "keep = 0"?
>            let isKeep = keep_attr || isGlobalKeep
>                vars' = if isKeep then mapIdOrTuple setKeepId vars else vars
>            -- mapM (\var -> traceM $ "ISDecl (3): \"" ++ pvpString var ++ "\" (" ++ pvpString typ ++ ")") vars'
>            return (ISDecl pos vars' (Just typ) [])

> pImperativePatternDecl :: ImperativeFlags -> SV_Parser ImperativeStatement
> pImperativePatternDecl flags =
>     do pos <- getPos
>        pat <- pPattern
>        ( (do pSymbol SV_SYM_eq
>              when (not (allowEq flags))
>                   (failWithErr
>                    (pos, EBadAssignEq (pvpString (stmtContext flags))))
>              exp <- pExpression
>              return (ISPatEq pos pat exp))
>         <|>
>          (do pSymbol SV_SYM_lt_minus
>              when (not (allowBind flags))
>                   (failWithErr
>                    (pos, EBadAssignBind (pvpString (stmtContext flags))))
>              exp <- pExpression
>              return (ISPatBind pos pat exp)))

> pImperativeLet :: Attributes -> Attributes -> ImperativeFlags -> Position
>                -> SV_Parser ImperativeStatement
> pImperativeLet decl_atts bind_atts flags pos =
>     do when (not (allowLet flags))
>             (failWithErr
>              (pos, EForbiddenLet (pvpString (stmtContext flags))))
>        vars <- pIdOrTuple
>        case (vars) of
>          Right i -> (pImperativeWithTypeAndVarInst bind_atts flags Nothing i)
>                     <|> doDefault pos vars
>          Left _ -> doDefault pos vars
>  where
>    doDefault pos vars =
>         do keep_attr <- attributes2keep decl_atts
>            -- XXX warn if we're overriding a "keep = 0"?
>            let isKeep = keep_attr || isGlobalKeep
>                vars' = if isKeep then mapIdOrTuple setKeepId vars else vars
>            -- mapM (\var -> traceM $ "ISDecl (4): \"" ++ pvpString var ++ "\" ()") vars'
>            return (ISDecl pos vars' Nothing [])

> data PortListArg =
>          Arg   CExpr
>        | Clock CExpr
>        | Reset CExpr
>        | Power CExpr

> pPortListArg :: SV_Parser PortListArg
> pPortListArg =
>       do pKeyword SV_KW_clocked_by
>          e <- pExpression
>          return (Clock e)
>     <|>
>       do pKeyword SV_KW_reset_by
>          e <- pExpression
>          return (Reset e)
>     <|>
>       do pKeyword SV_KW_powered_by
>          e <- pExpression
>          return (Power e)
>     <|>
>       do e <- pExpression
>          return (Arg e)

> pPortListArgs :: SV_Parser ([CExpr], Maybe CExpr, Maybe CExpr, Maybe CExpr)
> pPortListArgs = do
>         pos <- getPos
>         as <- pInParens (pCommaSep pPortListArg)
>         let findClock (Clock e) = [e]
>             findClock _         = []
>             findReset (Reset e) = [e]
>             findReset _         = []
>             findPower (Power e) = [e]
>             findPower _         = []
>             findArg   (Arg e)   = [e]
>             findArg   _         = []
>             (theClock,b1) = case concat(map findClock as) of
>                              []  -> (Nothing, False)
>                              [e] -> (Just e, False)
>                              _   -> (undefined,True)
>             (theReset,b2) = case concat(map findReset as) of
>                              []  -> (Nothing, b1)
>                              [e] -> (Just e, b1)
>                              _   -> (undefined,True)
>             (thePower, b) = case concat(map findPower as) of
>                              []  -> (Nothing, b2)
>                              [e] -> (Just e, b2)
>                              _   -> (undefined,True)
>             theArgs = concat(map findArg as)
>         when b (failWithErr (pos, EMultipleSpecialArgs))
>         return (theArgs, theClock, theReset, thePower)

> pImperativeWithTypeAndVarInst :: Attributes -> ImperativeFlags
>                               -> Maybe CType -> Id
>                               -> SV_Parser ImperativeStatement
> pImperativeWithTypeAndVarInst bind_atts flags typ ifcName =
>     do pSymbol SV_SYM_lparen
>        pSymbol SV_SYM_rparen
>                    <?> "() in a preceding interface declaration"
>        pSemi
>        pos <- getPos
>        when (not (allowInst flags))
>                 (failWithErr (pos, EForbiddenInstantiation
>                               (pvpString (stmtContext flags))))
>        var <- pVariable
>        params <- pParameters
>        statestring <- pWord
>        let instName = mkId pos (mkFString statestring)
>        (portLikeArgs, mClock, mReset, mPower) <- pPortListArgs
>        finalPos <- getPos
>        -- This used to report EMultipleInterfaces if ifcName was a tuple
>        when (null portLikeArgs)
>             (failWithErr (finalPos, ENoProvidedInterface))
>        let initPLargs = init portLikeArgs
>            finalArg = last portLikeArgs
>            constructor = cApply 16 var (params ++ initPLargs)
>        when (case (finalArg) of
>               (CVar i) -> i /= ifcName
>               _ -> True)
>             (failWithErr (finalPos, EBadFinalArg (pvpString finalArg)))
>        instprops <- attributes2instpprops bind_atts
>        return (ISInst pos instprops ifcName instName typ mClock mReset mPower constructor)

> pImperativeWithVar :: Attributes -> Attributes
>                    -> ImperativeFlags -> Position -> IdOrTuple
>                    -> SV_Parser ImperativeStatement
> pImperativeWithVar decl_atts bind_atts flags pos vars =
>     let noBindAttrs val = do assertEmptyAttributes EAttribsThisDecl bind_atts
>                              return val
>         noDeclAttrs val = do assertEmptyAttributes EAttribsThisDecl decl_atts
>                              return val
>         noAttrs val = noBindAttrs val >>= noDeclAttrs
>     in
>        ((pImperativeWithVarEq flags vars >>= noAttrs)
>         <|> (pImperativeWithVarBind bind_atts flags vars >>= noDeclAttrs)
>         <|> (pImperativeWithVarRegWrite flags pos vars >>= noAttrs)
>         <|> pImperativeWithVarDecl decl_atts bind_atts flags vars
>         <|> (pImperativeWithVarCall bind_atts flags vars >>= noDeclAttrs))
>         -- call also parses fields and suffixes
>         -- note: imperativeWithVarCall must come last,
>         --       because naked expressions are immediately successful.

> pImperativeWithExpr :: Attributes -> Attributes ->
>                     ImperativeFlags -> Position -> CExpr
>                     -> SV_Parser ImperativeStatement
> pImperativeWithExpr decl_atts bind_atts flags pos expr =
>     let noBindAttrs val = do assertEmptyAttributes EAttribsThisDecl bind_atts
>                              return val
>         noDeclAttrs val = do assertEmptyAttributes EAttribsThisDecl decl_atts
>                              return val
>         noAttrs val = noBindAttrs val >>= noDeclAttrs
>     in
>          (pImperativeWithExprBind bind_atts flags pos expr >>= noDeclAttrs)
>      <|> (pImperativeWithExprRegWrite flags pos expr >>= noAttrs)
>      <|> (pImperativeWithExprEq flags pos expr >>= noAttrs)
>      <|> (pImperativeWithExprCall flags pos expr >>= noAttrs)
>      <|> (pImperativeWithExprNakedExpr flags pos expr >>= noAttrs)


EXPRESSIONS

PREFIX AND INFIX OPERATORS

> pOperatorInto :: SV_Symbol -> (Position -> Id) -> SV_Parser Id
> pOperatorInto op idAt =
>     do pos <- getPos
>        pSymbol op <?> "operator"
>        return $ idAt pos

> type OpTableEntry = (SV_Symbol, Operator SV_Token SV_Parser_State CExpr)

> opPrefix :: SV_Symbol -> (Position -> Id) -> OpTableEntry
> opPrefix name opId = (name, Prefix (fmap f (pOperatorInto name opId)))
>     -- Leading minus sign is applied directly to the literal, so that it
>     -- is applied before the fromInteger or fromReal (so that -16 can be
>     -- assigned to Int#(5) even though the intermediate 16 can't be).
>     --
>     -- The same problem doesn't exist for the type Real, but we apply it
>     -- anyway for symmetry (and to not require an Arith instance).
>     --
>     -- Note that this also updates the position of the literal to start
>     -- with the minus sign.
>     --
>     -- Note that "pNumericLiteral" does this same transformation, if it is
>     -- lucky enough to get the plus/minus before it's parsed as a unary op.
>     where f op (CLit (CLiteral _ (LInt (IntLit w l v)))) |
>             getIdBaseString op == "negate" =
>               -- XXX when (v == 0) $ parseWarn (pos, WNegativeZeroIntLit)
>               (CLit (CLiteral (getPosition op) (LInt (IntLit w l (-v)))))
>           f op (CLit (CLiteral _ (LReal v))) |
>             getIdBaseString op == "negate" =
>               -- XXX when (v == 0) $ parseWarn (pos, WNegativeZeroIntLit)
>               (CLit (CLiteral (getPosition op) (LReal (-v))))
>           -- update the literals with leading plus
>           f op (CLit (CLiteral _ li)) |
>             getIdBaseString op == "id" =
>               (CLit (CLiteral (getPosition op) li))
>           f op arg = cVApply op [arg]

> opBinaryL :: SV_Symbol -> (Position -> Id) -> OpTableEntry
> opBinaryL name opId =
>     (name, Infix (fmap f (pOperatorInto name opId)) AssocLeft)
>     where f op left right = CBinOp left op right

> opTable :: [[OpTableEntry]]
> opTable =
>     [
>      -- the parser handles () [] :: and .
>      [opPrefix SV_SYM_plus idIdentityAt,
>       opPrefix SV_SYM_minus idNegateAt,
>       opPrefix SV_SYM_bang idNotAt,
>       opPrefix SV_SYM_tilde idInvertAt,
>       opPrefix SV_SYM_et idReduceAndAt,
>       opPrefix SV_SYM_pipe idReduceOrAt,
>       opPrefix SV_SYM_caret idReduceXorAt,
>       opPrefix SV_SYM_tilde_et idReduceNandAt,
>       opPrefix SV_SYM_tilde_pipe idReduceNorAt,
>       opPrefix SV_SYM_tilde_caret idReduceXnorAt,
>       opPrefix SV_SYM_caret_tilde idReduceXnorAt
>       -- prefix and suffix operators ++ and --
>      ],
>      [opBinaryL SV_SYM_star_star idStarStarAt],
>      [opBinaryL SV_SYM_star idStarAt,
>       opBinaryL SV_SYM_slash idSlashAt,
>       opBinaryL SV_SYM_percent idPercentAt],
>      [opBinaryL SV_SYM_plus idPlusAt, opBinaryL SV_SYM_minus idMinusAt],
>      [opBinaryL SV_SYM_lt_lt idLshAt, opBinaryL SV_SYM_gt_gt idRshAt
>       -- binaryl "<<<", binaryl ">>>"
>       ],
>      [opBinaryL SV_SYM_lt idLtAt, opBinaryL SV_SYM_lt_eq idLtEqAt,
>       opBinaryL SV_SYM_gt idGtAt, opBinaryL SV_SYM_gt_eq idGtEqAt],
>      -- "inside", "dist" are binary but don't work on expr, expr arguments
>      [opBinaryL SV_SYM_eq_eq idEqualAt, opBinaryL SV_SYM_bang_eq idNotEqualAt
>       -- binaryl "===", binaryl "!==",
>       -- binaryl "=?=", binaryl "!?="
>       ],
>      [opBinaryL SV_SYM_et idBitAndAt],
>      [opBinaryL SV_SYM_caret idCaretAt,
>       opBinaryL SV_SYM_tilde_caret idTildeCaretAt,
>       opBinaryL SV_SYM_caret_tilde idCaretTildeAt],
>      [opBinaryL SV_SYM_pipe idBitOrAt],
>      [opBinaryL SV_SYM_et_et idAndAt],
>      [opBinaryL SV_SYM_pipe_pipe idOrAt]
>      -- remaining are handled by the parser?
>     ]

XXX note that in SV binary ops take expressions, but prefix ones take primaries
XXX ++ and -- are special inc_dec, and inside/dist are just weird


expression parser without the ? : conditional operator

> pExpressionSimple :: SV_Parser CExpr
> pExpressionSimple =
>     buildExpressionParser (map (map snd) opTable) pPrimary

full-blown expression parser, including ? :

> pExpression :: SV_Parser CExpr
> pExpression = pCondExpressions >>= pExpressionWith
> -- pCondExpressions guarantees at least one result

> pExpressionWith :: [CQual] -> SV_Parser CExpr
> pExpressionWith [] = internalError "CVParser.pExpressionWith: []"
> pExpressionWith conds | all isCQFilter conds = -- expressions, ? optional
>     do questionPos <- getPos
>        pSymbol SV_SYM_question
>        e2 <- pExpression <?> "consequent expression"
>        pColon
>        e3 <- pExpression <?> "alternative expression"
>        return (mkIf questionPos conds e2 e3)
>    <|> return (joinWithAnd [expr | CQFilter expr <- conds])
> pExpressionWith conds = -- patterns, ? required
> -- XXX need better error: ? expected is not good enough
> -- XXX when we've parsed a matching-expression
>     do questionPos <- getPos
>        pSymbol SV_SYM_question
>        e2 <- pExpression <?> "consequent expression"
>        --colonPos <- getPos
>        pColon
>        e3 <- pExpression <?> "alternative expression"
>        return (mkIf questionPos conds e2 e3)

parse a "conditional" expression -- "<expr>" or "<expr> matches <pat>"

> pCondExpressions :: SV_Parser [CQual]
> pCondExpressions =
>     sepBy1 pCondExpression (pSymbol SV_SYM_et_et_et)
>     <|> pInParens pCondExpressions

XXX really we should permit parens, in pCondExpr ebut those would get eaten up
XXX by pExpressionSimple's call to pPrimary...
XXX making pCondExpression eat the parens would misparse
XXX   (x && y) || (z & q)
XXX and backtracking on parsing the expression would mean nasty errors in
XXX   (x && y) || (some syntax error)
XXX since the error reported would be based on cond-expr and unintelligible

> pCondExpression :: SV_Parser CQual
> pCondExpression = (pExpressionSimple >>= pCondExpressionWith)
>                   <?> "expression"

> pCondExpressionWith :: CExpr -> SV_Parser CQual
> pCondExpressionWith expr =
>         do pKeyword SV_KW_matches
>            pat <- pPattern <?> "pattern"
>            return (CQGen noType pat expr)
>     <|> return (CQFilter expr)


ACTIONS

XXX export the name, so we can make "action: foo; .. endaction" equivalent
XXX to let foo = action ... in BS Classic

> pActionExpr :: SV_Parser CExpr
> pActionExpr = pActionExprMaybeFunction [] Nothing

> pActionExprMaybeFunction :: Attributes -> Maybe (Id, [(Maybe CType, Id)]) -> SV_Parser CExpr
> pActionExprMaybeFunction attrs maybeNameArgs =
>     do pos <- getPos
>        (splitness, attrs') <- splitInAttributes attrs
>        let flags = actionFlags { functionNameArgs = maybeNameArgs }
>        block <- pImperativeNestedAction attrs' flags
>        expr <- imperativeToCExpr pos flags block
>        return $ fromMaybe expr (fmap (\wrapper -> wrapIf wrapper expr) splitness)

actions without "action .. endaction" (actionBlock and rule body)

> pActionsExprAt :: Position -> SV_Parser CExpr
> pActionsExprAt pos =
>     do block <- pImperativeNestedActionStmtsAt actionFlags pos
>        let flags = actionFlags { stmtContext = ISCExpression,
>                                  functionNameArgs = Nothing,
>                                  endKeyword = Nothing -- XXX
>                                }
>        imperativeToCExpr pos flags block

> pActionValueExpr :: SV_Parser CExpr
> pActionValueExpr = pActionValueExprMaybeFunction [] Nothing

> pActionValueExprMaybeFunction :: Attributes -> Maybe (Id, [(Maybe CType, Id)]) -> SV_Parser CExpr
> pActionValueExprMaybeFunction attrs maybeNameArgs =
>     do pos <- getPos
>        let flags = actionValueFlags { functionNameArgs = maybeNameArgs }
>        -- check for split attributes make a better error message / support them?
>        block <- pImperativeNestedActionValue attrs flags
>        imperativeToCExpr pos flags block

STATEMENT SEQUENCES (for turning into FSMs)

> pSequenceExpr :: SV_Parser CExpr
> pSequenceExpr =
>     do pos <- getPos
>        name <- pStartClause SV_KW_seq
>        pSequenceExpr2 pos True name
>    <|>
>     do pos <- getPos
>        name <- pStartClause SV_KW_par
>        pSequenceExpr2 pos False name

> pSequenceExpr2 :: Position -> Bool -> Maybe Id -> SV_Parser CExpr
> pSequenceExpr2 pos isSeq name =
>     do let seqFlags = (nullImperativeFlags { stmtContext = ISCSequence,
>                                              allowBind = True,
>                                              allowLoops = True,
>                                              allowConditionals = True,
>                                              allowReturn = True,
>                                              allowNakedExpr = True,
>                                              allowSubscriptAssign = True,
>                                              allowFieldAssign = True,
>                                              allowRegWrite = True })
>        block <- pImperativeStmts seqFlags
>        pEndClause (if isSeq then SV_KW_endseq else SV_KW_endpar) name
>        stmtts <- imperativeToStmtSeq ISCSequence block
>        let ps = posToString pos
>            theId = if isSeq then idSSeq else idSPar
>        return (cVApply (idSprime pos) [CCon (theId pos) [ps, stmtts]])


FUNCTIONS

parse optional array dimensions
If there are no dimensions return the original type
Otherwise transform the type to apply array the appropriate number of times

> pOptArrayDimensions :: CType -> SV_Parser CType
> pOptArrayDimensions typ =
>       do
>         let pArrBracket = do { pSymbol SV_SYM_lbracket; pSymbol SV_SYM_rbracket;
>                                getPos }
>         dimensions <- many pArrBracket
>         let mkArrayType pos typ =
>                -- mark the PrimArray constructor so that it can be peeled off
>                -- to reconstruct the base type (for multiple var decls)
>                let arr_con_id = addIdProp (idPrimArrayAt pos) IdPParserGenerated
>                in  cTApplys (cTCon arr_con_id) [typ]
>         return (foldr mkArrayType typ dimensions)


function argument, type is required

> pFunctionArg :: Bool -> SV_Parser (CType, Id, Maybe String)
> pFunctionArg bAllowPragmas =
>     (do (CField { cf_name = name,
>                   cf_type = CQType _ typ }) <- pFunctionPrototype
>         return (typ,name, Nothing))
>    <|>
>     (do prags <- if (bAllowPragmas)
>                   then pAttributes >>= attributes2PortName
>                   else (return Nothing )
>         typ <- pTypeExpr <?> "argument type"
>         -- XXX this used to accept "?"
>         var <- pIdentifier <?> "argument name"
>         typ' <- pOptArrayDimensions typ
>         return (typ', var, prags) )

> pFunctionArgOptType :: SV_Parser (Maybe CType, Id)
> pFunctionArgOptType =
>         do var1 <- pIdentifier
>            (-- has parameters, var1 is a type variable
>             do typ <- pTypeExprRequiredParamsWith (cTVar var1)
>                -- XXX this used to accept "?"
>                var2 <- pIdentifier <?> "argument name"
>                typ' <- pOptArrayDimensions typ
>                return (Just typ', var2)
>             <|>
>             -- followed by another identifier, var1 is a type variable
>             do -- XXX this used to accept "?"
>                var2 <- pIdentifier
>                typ' <- pOptArrayDimensions (cTVar var1)
>                return (Just typ', var2)
>             <|>
>             -- no identifier follows; var1 must be a value variable
>             return (Nothing, var1))
>     <|> do (typ, var, _) <- pFunctionArg False
>            return (Just typ, var)
>     -- XXX this used to accept "?" as an argument name (without a type)

> data FunctionType = FTFunction | FTMethod

get an expected end-keyword (hack for better error messages)

> fun_type_to_end_keyword :: FunctionType -> Maybe String
> fun_type_to_end_keyword FTFunction = Just "endfunction"
> fun_type_to_end_keyword FTMethod = Just "endmethod"

> pFunctionBody :: Position -- of function start
>               -> Id -- function name
>               -> [(Maybe CType, Id)] -- arguments and types (if specified)
>               -> FunctionType -- a function or a method?
>               -> (Bool {-isaction-}, Bool {-isav-})
>               -> SV_Parser CExpr
> pFunctionBody startPos name args fun_type (True, isActionValue) =
>     do let funNameArgs = Just (name, args)
>            flags = actionFlags { functionNameArgs = funNameArgs,
>                                  endKeyword =
>                                      fun_type_to_end_keyword fun_type }
>        block <- pImperativeNestedActionStmtsAt flags startPos
>        imperativeToCExpr startPos flags block
> pFunctionBody startPos name args fun_type (False, True) =
>     do let funNameArgs = Just (name, args)
>            flags = actionValueFlags { functionNameArgs = funNameArgs,
>                                       endKeyword =
>                                           fun_type_to_end_keyword fun_type }
>        block <- pImperativeNestedActionValueStmtsAt [] flags
>                 startPos
>        imperativeToCExpr startPos flags block
> pFunctionBody startPos name args fun_type (False, False) = do
>   attrs <- pAttributes
>   do
>         pActionExprMaybeFunction attrs (Just (name, args))
>     <|> pActionValueExprMaybeFunction attrs (Just (name, args))
>     <|> pImperativeExprBlock startPos attrs functionFlags
>         where functionFlags = (nullImperativeFlags
>                                { stmtContext = ISCExpression,
>                                  -- allow defining bound expressions
>                                  allowEq = True,
>                                  allowSubscriptAssign = True,
>                                  allowFieldAssign = True,
>                                  allowLet = True,
>                                  allowFunction = True,
>                                  allowConditionals = True,
>                                  allowLoops = True,
>                                  allowModule = True,
>                                  allowArrayDecl = True,
>                                  -- allow function specific stmts
>                                  allowReturn = True,
>                                  functionNameArgs = Just (name, args),
>                                  endKeyword =
>                                      fun_type_to_end_keyword fun_type })

pFunctionTail deals with a function prototype or definition from the point
just before the end of the signature (i.e. omitting the semicolon, or the "="
leading to the defining expression).  If isTypeClassItem is True, we are in a
field of a typeclass declaration, and a body is optional; otherwise we are in
a function definition, and a body must be present.

> pFunctionTail :: Position -> Bool -> Id -> [(Maybe CType, Id)] -> SV_Parser (Maybe CExpr)
> pFunctionTail startPos isTypeClassItem name args =
>    (do pSemi
>        ((do pos <- getPos
>             pKeyword SV_KW_provisos
>             failWithErr (pos, ESemiBeforeProvisos))
>         <|>
>         (do when (not isTypeClassItem) (fail "not typeclass item")
>             lookAhead (choice [pKeyword SV_KW_function,
>                                pKeyword SV_KW_module,
>                                pKeyword SV_KW_endtypeclass])
>             return Nothing)
>         <|>
>         (do expr <- (pFunctionBody startPos name args FTFunction
>                                                  (False, False))
>             pEndClause SV_KW_endfunction (Just name)
>             return (Just expr))))
>    <|>
>    (do pEq
>        expr <- pExpression
>        pSemi
>        return (Just expr))

> pFunctionAfterKeyword :: Position -> SV_Parser CDefl
> pFunctionAfterKeyword startPos =
>     do (maybeRetType, name) <- pFunctionNameOptType
>                                <?> "function return type or name"
>        args <- option [] (pInParens (pCommaSep pFunctionArgOptType))
>                <?> "function arguments"
>        let (argTypeMaybes, argIds) = unzip args
>            duplicateArgs = [(arg1, arg2)
>                             | (arg1:arg2:_) <- group $ sort $ argIds]
>        when (not (null duplicateArgs))
>                 (let (arg1, arg2) = head duplicateArgs
>                  in  failWithErr (getIdPosition arg2,
>                                   (EDuplicateFunctionArg (pvpString name)
>                                    (pvpString arg1) (getIdPosition arg1))))
>        context <- option [] pProvisos
>        mbody   <- pFunctionTail startPos False name args
>        body <- case mbody of
>                   Just e  -> return e
>                   Nothing -> failWithErr (startPos, EMissingFunctionBody)
>        -- return type and argument types may be omitted
>        -- if enough type information is provided, generate
>        -- a signed definition; otherwise an unsigned definition
>        let bodyClause = CClause (map CPVar argIds) [] body
>            maybeTypes = sequence (maybeRetType:argTypeMaybes)
>        def <- case maybeTypes of
>                  Just (retType:argTypes) ->
>                      let methType = CQType context
>                                     (foldr fn retType argTypes)
>                          def = CDef name methType [bodyClause]
>                      in  return $ CLValueSign def []
>                  Nothing -> do
>                      let hasArgType = any isJust argTypeMaybes
>                          hasRetType = isJust maybeRetType
>                      when (hasArgType || hasRetType) $
>                          parseWarn (startPos, WTypesIgnored "function")
>                      return $ CLValue name [bodyClause] []
>                  Just [] -> internalError ("CVParser.pFunctionAfterKeyword"
>                                            ++ ".def: "
>                                            ++ "sequence returned Just []")
>        return def

> pFunctionPrototypeWithArgs :: SV_Parser (CField, [(Maybe CType, Id)])
> pFunctionPrototypeWithArgs =
>     do pos <- getPos
>        pKeyword SV_KW_function <?> "function definition"
>        rettype <- pTypeExpr <?> "function return type"
>        name <- pIdentifier <?> "function name"
>        args <- option [] (pInParens (pCommaSep (pFunctionArg False)))
>                <?> "function arguments"
>        let (argtypes, argids, _ ) = unzip3 args
>            methtype = CQType [] (foldr fn rettype argtypes)
>        return (CField { cf_name = name,
>                         cf_pragmas = Just [(PIArgNames argids)],
>                         cf_orig_type = Nothing,
>                         cf_type = methtype,
>                         cf_default = []
>                       },
>                map (\ (x,y,_)->(Just x,y)) args)

> pFunctionPrototype :: SV_Parser CField
> pFunctionPrototype =
>     do (x,_) <- pFunctionPrototypeWithArgs
>        return x

> pTypeclassFunction :: SV_Parser CField
> pTypeclassFunction =
>     do startPos <- getPos
>        (funProto,args) <- pFunctionPrototypeWithArgs
>        let (_, argIds) = unzip args
>        mbody <- pFunctionTail startPos
>                               True
>                               (cf_name funProto)
>                                args
>        case mbody of
>           Nothing -> return funProto
>           Just e -> return funProto{ cf_default =
>                                       [CClause (map CPVar argIds) [] e]}

> pImperativeForeignFunctionAt :: Position -> Attributes -> ImperativeFlags
>                              -> SV_Parser [ImperativeStatement]
> pImperativeForeignFunctionAt pos atts flags =
>     -- "import" has already been parsed
>     do pTheQuotedString "BDPI" <?> "\"BDPI\""
>        when (not (allowForeign flags))
>            (failWithErr (pos, EForbiddenForeignFunction
>                                 (pvpString (stmtContext flags))))
>        assertEmptyAttributes EAttribsForeignFunction atts
>        -- optional linkage name, then "="
>        maybe_link_name <- ( do f <- pForeignFunctionLinkName
>                                pEq
>                                return (Just f)
>                            <|>
>                             return Nothing
>                           )
>        -- function prototype
>        -- XXX this requires names for the arguments
>        proto <- pFunctionPrototype
>        let bsv_name = cf_name proto
>        -- pFunctionPrototype doesn't parse provisos
>        let (CQType _ basetype) = cf_type proto
>        -- the pragmas in "proto" are for naming, so we ignore them
>        provisos <- option [] pProvisos
>        pSemi
>        let link_name = fromMaybe bsv_name maybe_link_name
>        let bsv_type = (CQType provisos basetype)
>        return [ISForeignFunction pos bsv_name link_name bsv_type]

> pForeignFunctionLinkName :: SV_Parser Id
> pForeignFunctionLinkName =
>     do pos <- getPos
>        name <- pWord <?> "linkage name"
>        return (mkId pos (mkFString name))


MODULES

A module parameter, which returns an identifier and type along
with a PPparam pragma for the module indicating if this module
argument should become a Verilog parameter.

> pModuleParam :: SV_Parser ((Id, CType), [PProp])
> pModuleParam =
>     do attr_props <- pAttributes >>= handleModuleParamAttrs
>        isParam <- option False (pKeyword SV_KW_parameter >> return True)
>        let mkPProps i = (if isParam then [PPparam [i]] else [])
>                         ++ map (addPragmaId i) attr_props
>        ( (do (CField { cf_name = name,
>                        cf_type = (CQType _ typ) }) <- pFunctionPrototype
>              -- XXX functions can't be params! but compiler won't allow
>              -- XXX this to synthesize anyway (even to ports)
>              return ((name, typ), mkPProps name))
>         <|>
>          (do t <- pTypeExpr <?> "parameter type"
>              i <- pIdentifier <?> "parameter name"
>              t'<- pOptArrayDimensions t
>              return ((i,t'), mkPProps i))
>         )


A non-parameter module argument, which returns an identifier and
type along with pragmas indicating special information about
the ports created for the argument (clock port names, gates, etc.).

> pPortlikeArg :: SV_Parser ((Id, CType), [PProp])
> pPortlikeArg =
>     (do (CField { cf_name = name,
>                   cf_type = (CQType _ typ) }) <- pFunctionPrototype
>         return ((name,typ), []))
>    <|>
>     (do pprops <- pAttributes >>= handleModuleArgAttrs
>         typ <- pTypeExpr <?> "argument type"
>         -- XXX this used to accept "?"
>         var <- pIdentifier <?> "argument name"
>         typ' <- pOptArrayDimensions typ
>         return ((var, typ'), map (addPragmaId var) pprops))

> pModuleParams :: (Position -> (CType,[CPred])) -> SV_Parser ([(Id, CType)], CType, [PProp])
> pModuleParams tc = do
> -- Note: called only when any preds added by substMonadType will already be
> -- taken care of; so they can be ignored here.
>     (params, itft, param_pps) <- pModuleParams2
>     let f (v,t) =
>          let (t1,_) = substMonadType tc t
>          in (v,t1)
>         (itft2,_) = substMonadType tc itft
>     return (map f params, itft2, param_pps)
>
> pModuleParams2 :: SV_Parser ([(Id, CType)], CType, [PProp])
> pModuleParams2 = do
>     -- module args that should become params are indicated with a pprop
>     param_info <- option [] (pSymbol SV_SYM_hash >>
>                              pInParens (pCommaSep1 pModuleParam))
>     let (params, param_pps) = apSnd concat (unzip param_info)
>     let emptyIfcAt pos = cTCon (mkQId pos fsPrelude fsEmptyIfc)
>         ifcTypeExpr = do -- interface defaults to Prelude.Empty
>             ipos <- getPos
>             typ <- option (emptyIfcAt ipos) pTypeExpr
>             return (Just typ)
>         ifcType = pInParens ifcTypeExpr <?> "module interface"
>     ifctm <- option Nothing (try ifcType)
>     case ifctm of
>        Nothing -> do
>          ifs <- pInParens (pCommaSep1 pPortlikeArg) <?> "dynamic (port-like) args"
>          let arg_info = init ifs
>              ((ifc,itft),ifc_pps) = last ifs
>              (args, arg_pps) = apSnd concat (unzip arg_info)
>          when (not (null ifc_pps))
>               (failWithErr (getPosition ifc,
>                             EAttributeOnWrongArgType (getModulePragmaName (head ifc_pps))
>                                                      (getIdBaseString ifc)
>                                                      "an interface"))
>          return (params ++ args, itft, param_pps ++ arg_pps)
>        Just itft -> return (params, itft, param_pps)

> pModuleExpression :: SV_Parser CExpr
> pModuleExpression =
>           do pos <- getPos
>              pKeyword SV_KW_module <?> "module expression"
>              its <- pTypeParametersNonOptional
>              pSemi
>              when (length its > 1) (failWithErr (pos, EBadInterface))
>              let pModEnd = pKeyword SV_KW_endmodule
>              body <- pModuleBody pos ISCIsModule pModEnd
>                                  (Just (head its)) [] -- XXX consider allowing attributes
>              return body

> pModuleBody :: Position -> ISContext -> SV_Parser () ->
>                (Maybe CType) -> [CSchedulePragma] -> SV_Parser CExpr
> pModuleBody pos ctxt pModEnd mifct sprags =
>           do let impFlags = (nullImperativeFlags { stmtContext = ctxt,
>                                                    ifcType = mifct,
>                                                    allowEq = True,
>                                                    allowSubscriptAssign =
>                                                                         True,
>                                                    allowFieldAssign = True,
>                                                    allowArrayDecl = True,
>                                                    allowFunction = True,
>                                                    allowBind = True,
>                                                    allowLoops = True,
>                                                    allowConditionals = True,
>                                                    allowNakedExpr = True,
>                                                    allowRule = True,
>                                                    allowMethod = True,
>                                                    allowSubinterface = True,
>                                                    allowModule = True,
>                                                    allowLet = True,
>                                                    -- XXX should "return" be
>                                                    -- XXX something else?
>                                                    allowReturn = True,
>                                                    allowSequence = True,
>                                                    allowProperty = True,
>                                                    allowAssert = True,
>                                                    allowCover = True,
>                                                    allowInst = True })
>              pBody pos pModEnd mifct sprags impFlags

> pBody :: Position -> SV_Parser () -> (Maybe CType) -> [CSchedulePragma] ->
>             ImperativeFlags -> SV_Parser CExpr
> pBody pos pModEnd mifct sprags flags =
>     do body <- pImperativeStmtBlock flags pModEnd >>= cstmtsToCMStmts sprags
>        let fixIfcPos (CMinterface (Cinterface _ name def)) =
>                         CMinterface (Cinterface pos name def)
>            fixIfcPos stmt = stmt
>            fixedIfcPosBody = map fixIfcPos body
>        return (Cmodule pos fixedIfcPosBody)

> pBVIModuleBody :: Position -> CExpr -> SV_Parser () ->
>                    (Maybe CType) -> [CSchedulePragma] -> SV_Parser [CMStmt]
> pBVIModuleBody pos filestring pModEnd mifct sprags =
>           do let impFlags = (nullImperativeFlags { stmtContext = ISCBVI,
>                                                    ifcType = mifct,
>                                                    filestr = Just filestring,
>                                                    allowEq = True,
>                                                    allowSubscriptAssign =
>                                                                         True,
>                                                    allowFieldAssign = True,
>                                                    allowArrayDecl = True,
>                                                    allowFunction = True,
>                                                    allowBind = True,
>                                                    allowLoops = True,
>                                                    allowConditionals = True,
>                                                    allowNakedExpr = True,
>                                                    allowRule = True,
>                                                    allowModule = True,
>                                                    allowLet = True,
>                                                    allowSequence = True,
>                                                    allowProperty = True,
>                                                    allowAssert = True,
>                                                    allowCover = True,
>                                                    allowInst = True
>                                                  })
>              body <- pImperativeStmtBlock impFlags pModEnd >>= cstmtsToCMStmts sprags
>              let fixIfcPos (CMinterface (Cinterface _ name def)) =
>                      CMinterface (Cinterface pos name def)
>                  fixIfcPos stmt = stmt
>              return (map fixIfcPos body)

> pImperativeModule :: Attributes -> ImperativeFlags
>                   -> SV_Parser [ImperativeStatement]
> pImperativeModule atts flags =
>           do pos <- getPos
>              pKeyword SV_KW_module <?> "module definition"
>              -- jes
>              ( try
>                 (do mCMonadType <-
>                      option Nothing
>                       (fmap Just (pInBrackets pTypeExpr))
>                     ((-- Check for "#" (i.e. using "module" keyword as a type
>                       -- expression), and continue parsing accordingly
>                       -- Note that since "module" will be of kind (* -> *), this is
>                       -- the *only* way it can thus be used at the start of a stmt.
>                       do when (isJust mCMonadType) (fail "# not allowed here")
>                          pars <- pTypeParametersNonOptional
>                          let typ = cTApplys (TDefMonad pos) pars
>                          -- module will likely never be the result of a bind,
>                          -- but let's allow it anyway:
>                          let (bind_atts, decl_atts) = partition isBindAttrib atts
>                          stmt <- pImperativeWithType decl_atts bind_atts flags typ
>                          stmts <- pImperativeDeclOrAssign2
>                                       decl_atts bind_atts flags True stmt
>                          pImperativeDeclOrAssignSemi2 flags stmts
>                      )
>                      <|>
>                      (do name <- pIdentifier <?> "module name"
>                          when (not (allowModule flags))
>                                     (failWithErr (pos, EForbiddenModule
>                                                        (pvpString (stmtContext flags))))
>                          (attr_props,sprags) <- attributes2modpprops atts
>                          let (ctxt,tc@(monadType,context')) = case mCMonadType of
>                                                                      Nothing -> (ISCIsModule, defaultModuleMonadInfo pos)
>                                                                      Just (TDefMonad _) -> (ISCIsModule, defaultModuleMonadInfo pos)
>                                                                      Just t -> (ISCModule t, (t,[]))
>                          (params, ifcType, param_props) <- pModuleParams (\ pos -> tc)

>                          context <- fmap (context' ++) (option [] pProvisos)
>                          pSemi
>                          let pModEnd = pEndClause SV_KW_endmodule (Just name)
>                          mod <- pModuleBody pos ctxt pModEnd (Just ifcType) sprags
>                          let resultType = cTApplys monadType [ifcType]
>                              (paramIds, paramTypes) = unzip params
>                              modType = CQType context (foldr fn resultType paramTypes)
>                              defClause = CClause (map CPVar paramIds) [] mod
>                              props = attr_props ++ param_props
>                              prag = if null props then Nothing
>                                     else Just (Pproperties name props)
>                          -- we don't check module pragmas here,
>                          -- we check them in GenWrap after we have the
>                          -- symbol table and have expanded Vectors
>                          return [ISModule pos name prag modType defClause]
>                      ))))

a "module verilog":

> pMethodConflictOp :: SV_Parser MethodConflictOp
> pMethodConflictOp =
>     do p <- getPos
>        w <- pWord <?> "scheduling operator"
>        let mx = case w of
>                  "CF" -> Just CF
>                  "SB" -> Just SB
>                  "SBR" -> Just SBR
>                  "ME" -> Just ME
>                  "P" -> Just P
>                  "C" -> Just C
>                  "EXT" -> Just EXT
>                  otherwise  -> Nothing
>        when (isNothing mx) (failWithErr (p, EBadMethodConflictOp))
>        return (fromJust mx)

> pVMethodConflict :: SV_Parser ([Id], MethodConflictOp, [Id])
> pVMethodConflict =
>     do pos <- getPos
>        -- pTheString "schedule" -- (now already read)
>        i1s <- option [] (fmap (:[]) pDottedName <|> pInParens (pCommaSep pDottedName))
>        posOp <- getPos
>        op  <- pMethodConflictOp
>        when ((not (null i1s)) && (op==ME || op==EXT)) (failWithErr (posOp, EBadMethodConflictOpList))
>        i2s <- fmap (:[]) pDottedName <|> pInParens (pCommaSep pDottedName)
>               <?> "scheduling name(s)"
>        pSemi
>        return (i1s, op, i2s)

> pGroup :: SV_Parser [Longname]
> pGroup = (fmap (:[]) pCompoundIdentifier
>           <|> pInParens (pCommaSep pCompoundIdentifier))
>

> pMethodConflict :: Bool -> SV_Parser ([Longname], MethodConflictOp, [Longname])
> pMethodConflict doingPreempts =
>     do let nakedElement = do
>              pos <- getPos
>              i1s <- option [] pGroup
>              posOp <- getPos
>              op  <- (if doingPreempts
>                       then do pSymbol SV_SYM_comma
>                               return CF -- CF irrelevant, but must be something
>                       else pMethodConflictOp )
>              when ((not (null i1s)) && (op==ME || op==EXT))
>                   (failWithErr (posOp, EBadMethodConflictOpList))
>              i2s <- pGroup
>                     <?> "scheduling name(s)"
>              return (i1s, op, i2s)
>        nakedElement

> pVExpr :: SV_Parser (CExpr, Bool) -- Bool says it's binding, rather than eq definition
> pVExpr =
>     do pos <- getPos
>        isBinding <-
>          ( do pSymbol SV_SYM_lt_minus
>               return True
>           <|>
>            do pSymbol SV_SYM_eq
>               return False
>          )
>        e <- pExpression
>        return (e, isBinding)

> pVArgParam :: SV_Parser (V.VArgInfo, CExpr, Bool)
> pVArgParam =
>     do pos <- getPos
>        n <- pVName
>        (e,b) <- pVExpr
>        pSemi
>        return (V.Param n, e, b)

> pVArgPort :: SV_Parser (V.VArgInfo, CExpr, Bool)
> pVArgPort =
>     do pos <- getPos
>        -- same allowed properties as a method argument
>        let allowed_props = [("reg",    V.VPreg),
>                             ("unused", V.VPunused)]
>        (n, pps) <- pVeriPort "a module port" allowed_props
>        (mclk, mrst) <- pVArgPortOptions
>        (e,b) <- pVExpr
>        pSemi
>        return (V.Port (n,pps) mclk mrst, e, b)

> data ArgPortOption =
>          PortClock Id
>        | PortReset Id

> pVArgPortOption :: SV_Parser ArgPortOption
> pVArgPortOption =
>       do pKeyword SV_KW_clocked_by
>          c <- pInParens pDottedName
>          return (PortClock c)
>     <|>
>       do pKeyword SV_KW_reset_by
>          r <- pInParens pDottedName
>          return (PortReset r)

> pVArgPortOptions :: SV_Parser (Maybe Id, Maybe Id)
> pVArgPortOptions =
>     do pos <- getPos
>        opts <- many pVArgPortOption
>        let findClock (PortClock c) = [c]
>            findClock _             = []
>            findReset (PortReset r) = [r]
>            findReset _             = []
>        mclk <- case (concatMap findClock opts) of
>                    []  -> return Nothing
>                    [c] -> return (Just c)
>                    _   -> failWithErr (pos, EBVIMultipleOpts "clocked_by")
>        mrst <- case (concatMap findReset opts) of
>                    []  -> return Nothing
>                    [r] -> return (Just r)
>                    _   -> failWithErr (pos, EBVIMultipleOpts "reset_by")
>        return (mclk, mrst)

> pVPath :: SV_Parser (V.VName, V.VName)
> pVPath =
>     do pos <- getPos
>        -- pTheString "path" -- (now already read)
>        let pPair = do i1 <- pVName
>                       pSymbol SV_SYM_comma
>                       i2 <- pVName
>                       return (i1,i2)
>        x <- pInParens pPair
>        pSemi
>        return x

> pVClockPair :: SV_Parser (Id, Id)
> pVClockPair =
>     do pos <- getPos
>        let pPair = do i1 <- pDottedName
>                       pSymbol SV_SYM_comma
>                       i2 <- pDottedName
>                       return (i1,i2)
>        x <- pInParens pPair
>        pSemi
>        return x

> mkMethodConflictInfo :: [([Longname], MethodConflictOp, [Longname])] ->
>                         MethodConflictInfo Longname
> mkMethodConflictInfo scheds =
>     let f b = [(i1,i2)
>                | (i1s,bb,i2s) <- scheds, b==bb, i1<-i1s, i2<-i2s]
>         g b = [i2s
>                | (i1s,bb,i2s) <- scheds, b==bb]
>         h b = [i2
>                | (i1s,bb,i2s) <- scheds, b==bb, i2<-i2s]
>     in MethodConflictInfo (f CF) (f SB) (g ME) (f P) (f SBR) (f C) (h EXT)

> pClockLine :: SV_Parser (Maybe Id, [(V.VName, Maybe V.VName)])
>       -- the Id is the BSV method name (current clock by default)
>       -- the Maybe String is the gate port, if present.
>       -- It will be a failure if the gate port is absent, but the method has a gate wire.
> pClockLine =
>     do pos <- getPos
>        pTheString "clock"
>        methodName <- option Nothing (fmap Just pIdentifier)
>        ports <- pInParens (pCommaSep1 pVName)
>        pSemi
>        case ports of
>           [cl] -> return (methodName , [(cl,Nothing)])
>           [cl,gt] -> return (methodName, [(cl, Just gt)])
>           _ ->  (failWithErr (pos, EInvalidNoOfClocks))

> mkClockMethods :: [(Maybe Id, [(V.VName, Maybe V.VName)])] -> [V.VFieldInfo]
> mkClockMethods =
>     let g (s,Nothing) = [(s,[])]
>         g (s,Just g) = [(s,[]),(g,[])]
>         f (Nothing, _) = []
>         f (Just i , cmg) = [V.Method i Nothing Nothing 1 (concat(map g cmg)) Nothing Nothing]
>     in concat . (map f)

> pImperativeForeignModuleAt :: Position -> Attributes -> ImperativeFlags
>                            -> SV_Parser [ImperativeStatement]
> pImperativeForeignModuleAt pos atts flags =
>            -- "import" has already been parsed
>            do pTheQuotedString "BVI" <?> "\"BVI\""
>               when (not (allowForeign flags))
>                        (failWithErr (pos, EForbiddenForeignModule
>                                      (pvpString (stmtContext flags))))
>               let whichModule = option (defaultModuleMonadInfo pos)
>                                        (fmap (\x -> (x,[])) (pInBrackets pTypeExpr))
>               (filename,name,context', monadType) <-
>                    ( do pKeyword SV_KW_module <?> "module symbol"
>                         (t,c) <- whichModule
>                         n <- pIdentifier <?> "module name"
>                         return (getIdString n,n,c,t)
>                     <|>
>                      do f <- pWord <?> "file name"
>                         pEq
>                         pKeyword SV_KW_module <?> "module symbol"
>                         (t,c) <- whichModule
>                         n <- pIdentifier <?> "module name"
>                         return (f,n,c,t)
>                    )
>
>               -- check for command-line synthesis of import "BVI"
>               let nameStr = getIdString name
>               bscFlags <- getParserFlags
>               when (nameStr `elem` (genName bscFlags)) $
>                    failWithErr (pos, EForeignModSynth nameStr)
>
>               let filestring = stringLiteralAt pos filename
>               (params, ifcType, _) <- pModuleParams (\ pos -> (monadType,context'))
>               context <- fmap (context' ++) (option [] pProvisos)
>               pSemi
>               let resultType = cTApplys monadType [ifcType]
>                   (paramIds, paramTypes) = unzip params
>                   modType = CQType context (foldr fn resultType paramTypes)
>               let pModEnd = pEndClause SV_KW_endmodule (Just name)
>               body <- pBVIModuleBody pos filestring pModEnd (Just ifcType) []
>               when (null body)
>                    (failWithErr (pos, EForeignModEmptyBody))
>               let defClause = CClause (map CPVar paramIds) [] (Cmodule pos body)
>               pragmas <- attributes2ForeignModPragma name atts
>               return [ISForeignModule pos name modType defClause pragmas]

PACKAGES

> pImperativeExport :: Attributes -> ImperativeFlags
>                   -> SV_Parser [ImperativeStatement]
> pImperativeExport atts flags =
>     do pos <- getPos
>        pKeyword SV_KW_export
>        when (not (allowExport flags))
>                 (failWithErr (pos, EForbiddenExport
>                               (pvpString (stmtContext flags))))
>        assertEmptyAttributes EAttribsExport atts
>        exports <- pCommaSep1 pExportItem
>        pSemi
>        return [ISExport pos exports]

> pExportItem :: SV_Parser CExport
> pExportItem =
>     -- This should probably check for all possibilities:
>     --  (1) <pkg>::*
>     --  (2) [<pkg>::]var
>     --  (3) [<pkg>::]Con[(..)]
>     -- where "pkg" can be upper or lowercase.
>     -- Right now, we don't support the qualifiers in #2 and #3,
>     -- and don't give a directed error message if the user tries it.
>     -- Because of the overlap in parsing, we use try the package first.
>     (try pExportPackage) <|> pExportConstructor <|> pExportIdentifier

> pExportConstructor :: SV_Parser CExport
> pExportConstructor =
>     do name <- pConstructor <?> "export item"
>        all <- option False
>               (pInParens (pSymbol SV_SYM_dot_dot >> return True))
>        return ((if all then CExpConAll else CExpCon) name)

> pExportIdentifier :: SV_Parser CExport
> pExportIdentifier =
>     do name <- pIdentifier <?> "export item"
>        return (CExpVar name)

> pExportPackage :: SV_Parser CExport
> pExportPackage =
>     do pkgPos <- getPos
>        pkg <- pWord <?> "package name"
>        pSymbol SV_SYM_colon_colon
>        -- XXX do something or error if a name is found instead of star?
>        pSymbol SV_SYM_star
>        return (CExpPkg (mkId pkgPos (mkFString pkg)))

> pImperativeImportOrForeign :: Attributes -> ImperativeFlags
>                               -> SV_Parser [ImperativeStatement]
> pImperativeImportOrForeign atts flags =
>     do pos <- getPos
>        pKeyword SV_KW_import
>        ((pImperativeForeignModuleAt pos atts flags <?> "foreign module")
>         <|> (pImperativeForeignFunctionAt pos atts flags <?> "foreign function")
>         <|> (pImperativeImportAt pos atts flags <?> "import"))

> pImperativeImportAt :: Position -> Attributes -> ImperativeFlags
>                     -> SV_Parser [ImperativeStatement]
> pImperativeImportAt pos atts flags =
>     do names <- pCommaSep1 pImportItem
>        when (not (allowImport flags))
>                 (failWithErr (pos, EForbiddenImport
>                               (pvpString (stmtContext flags))))
>        assertEmptyAttributes EAttribsImport atts
>        pSemi
>        return [ISImport pos names]

> pImportItem :: SV_Parser Id
> pImportItem =
>     do pkgPos <- getPos
>        pkg <- pWord <?> "package name"
>        pSymbol SV_SYM_colon_colon
>        (pSymbol SV_SYM_star >> return (mkId pkgPos (mkFString pkg)))
>         <|>
>         do pos <- getPos
>            var <- pWord <?> "imported identifier"
>            (failWithErr (pos, EUnsupportedImport pkg var))

Some of the topdefs (modules and functions) may be preceded by attributes.  To
avoid backtracking, we read the attributes first, and supply them as
parameters to the parsers that might take them.

> pPackageDecl :: SV_Parser Id
> pPackageDecl =
>     do pKeyword SV_KW_package
>        namePos <- getPos
>        name <- pWord <?> "package name"
>        pSemi
>        return (mkId namePos (mkFString name))

> pPackage :: String -> SV_Parser CPackage
> pPackage defaultPkgName =
>     do startPos <- getPos
>        let defaultPkgId = mkId startPos (mkFString defaultPkgName)
>        -- package is optional; package name defaults to file name otherwise
>        pkgId <- option Nothing (fmap Just pPackageDecl)
>                 <?> "package declaration"
>        let toplevelFlags = (nullImperativeFlags { stmtContext = ISCToplevel,
>                                                   allowEq = True,
>                                                   allowArrayDecl = True,
>                                                   allowFunction = True,
>                                                   allowModule = True,
>                                                   allowInterface = True,
>                                                   allowForeign = True,
>                                                   allowTypedef = True,
>                                                   allowTypeclass = True,
>                                                   allowInstanceDecl = True,
>                                                   allowExport = True,
>                                                   allowImport = True })
>        stmts <- pImperativeStmts toplevelFlags
>        let name = maybe defaultPkgId id pkgId
>            (importStmts, stmtsNoImports) = partition isISImport stmts
>            (exportStmts, stmtsNoImportsExports) =
>                partition isISExport stmtsNoImports
>            importPkgs = concat [pkgs | ISImport _ pkgs <- importStmts]
>            imports = [CImpId False pkg | pkg <- importPkgs]
>            selfImports = [pkg | pkg <- importPkgs, pkg == name]
>            exportedIds = concat [ids | ISExport _ ids <- exportStmts]
>            exports = if null exportedIds then Right [] else Left exportedIds
>            -- endpackage is only required if the package was specified
>            endpackage = maybe (return ())
>                         (pEndClause SV_KW_endpackage . Just) pkgId
>        when (not (null selfImports)) -- prohibit importing self
>             (let badImp = head selfImports
>                  badImpPos = getPosition badImp
>                  emsg = ECircularImports [pvpString badImp]
>              in  failWithErr (badImpPos, emsg))
>        defs <- imperativeToCDefns stmtsNoImportsExports
>        endpackage
>        eof svTokenToString
>        return $ CPackage name exports imports [] [] defs []

parse a package and return warnings accumulated by parser

> pPackageWithWarnings :: String -> SV_Parser (CPackage, [WMsg])
> pPackageWithWarnings defaultPkgName =
>     do pkg <- pPackage defaultPkgName
>        warns <- getParseWarnings
>        return (pkg, reverse warns)


=========

Attribute Instances

> data AttValue = AVNum Position Integer
>                 | AVString Position String
>                 | AVList Position [AttValue]
>          deriving (Show)

> instance Eq AttValue where
>   (==) (AVNum _ i1) (AVNum _ i2)       = (i1 == i2)
>   (==) (AVString _ s1) (AVString _ s2) = (s1 == s2)
>   (==) (AVList _ l1) (AVList _ l2)     = (l1 == l2)
>   (==) _ _                             = False

> data Attribute = Attribute { attr_name :: Id, attr_value :: AttValue }
>          deriving (Eq, Show)

> type Attributes = [Attribute]

> instance HasPosition Attribute where
>   getPosition (Attribute name _) = getPosition name

> instance HasPosition AttValue where
>   getPosition (AVNum p _) = p
>   getPosition (AVString p _) = p
>   getPosition (AVList p _) = p

parse attributes

> pAttValue :: SV_Parser AttValue
> pAttValue = do
>   pos <- getPos
>   (fmap (AVNum pos) pDecimal -- XXX perhaps should be any numeric literal
>            <|>
>            fmap (AVString pos) pQuotedString
>            <|>
>            fmap (AVList pos) (pInBraces (pCommaSep (pAttValue <?> "value in list"))))
>           <?> "attribute value"

> pAttribute :: SV_Parser Attribute
> pAttribute =
>     do namePos <- getPos
>        name <- (pWord)
>               <|>
>                (pKeyword SV_KW_clocked_by >> return "clocked_by")
>               <|>
>                (pKeyword SV_KW_reset_by >> return "reset_by")
>               <|>
>                (pKeyword SV_KW_parameter >> return "parameter")
>        value <- option (AVNum namePos 1) (pEq >> pAttValue)
>        return (Attribute (mkId namePos (mkFString name)) value)

> pAttributes :: SV_Parser Attributes
> pAttributes =
>   do attr_lines <-
>        (many (do pSymbol SV_SYM_lparen_star <?> "attributes"
>                  atts <- pCommaSep (pAttribute <?> "attribute")
>                  pSymbol SV_SYM_star_rparen <?> "end of attribute list"
>                  return atts))
>      return (concat attr_lines)

attribute utilities

> isBindAttrib :: Attribute -> Bool
> isBindAttrib (Attribute name value) = (getIdString name == "doc" ||
>                                        getIdString name == "inst_name" ||
>                                        getIdString name == "hide" ||
>                                        getIdString name == "hide_all")

> assertEmptyAttributes :: ErrMsg -> Attributes -> SV_Parser ()
> assertEmptyAttributes err [] = return ()
> assertEmptyAttributes err (attr:_) = failWithErr (getPosition attr, err)

> reportDeprecatedAttributeName :: [(String, String)] -> [(String, String)] ->
>                                  Attributes -> SV_Parser Attributes
> reportDeprecatedAttributeName deps obs attrs =
>   let lookupAttr lst a =
>           let pos = getPosition a
>               str = getIdString (attr_name a)
>           in  case (lookup str lst) of
>                   Nothing -> Nothing
>                   Just new_str  -> Just (pos, str, new_str)
>       warn_about = mapMaybe (lookupAttr deps) attrs
>       err_about  = mapMaybe (lookupAttr obs) attrs
>       fix_name a = let nm = attr_name a
>                        fs = [ a { attr_name = (setIdBaseString nm new_str) }
>                             | (_,str,new_str) <- warn_about
>                             , str == getIdString (attr_name a)
>                             ]
>                    in if (null fs) then a else (head fs)
>       corrected_attrs = map fix_name attrs
>   in case (err_about, warn_about) of
>        ([], []) -> return attrs
>        ([], ws) -> do
>            let mkMsg new_str = "It has been replaced by " ++
>                                quote new_str ++ "."
>            mapM_ parseWarn
>                [ (pos, WDeprecated "attribute" str (mkMsg new_str))
>                     | (pos,str,new_str) <- ws ]
>            return corrected_attrs
>        (((pos,str,new_str):_),_) ->
>            let mkMsg new_str = "Instead use " ++ quote new_str ++ "."
>            in  failWithErr (pos, EObsolete "attribute" str (mkMsg new_str))

> reportBadAttributeName :: String -> [String] -> [String] -> Attributes ->
>                           SV_Parser ()
> reportBadAttributeName loc allowed hidden attrs =
>   let all_allowed = allowed ++ hidden
>       toStr a = getIdString (attr_name a)
>       bad_attrs = filter (\a -> (toStr a) `notElem` all_allowed) attrs
>   in  case (bad_attrs) of
>         [] -> return ()
>         (a:_) -> let pos = getPosition a
>                      name = getIdString (attr_name a)
>                  in  failWithErr (pos, EBadAttributeName name loc allowed)

> -- when the only attributes are hidden
> reportBadAttributeNameNoAllowed :: ErrMsg -> [String] -> Attributes ->
>                                    SV_Parser ()
> reportBadAttributeNameNoAllowed errmsg hidden attrs =
>   let all_allowed = hidden
>       toStr a = getIdString (attr_name a)
>       bad_attrs = filter (\a -> (toStr a) `notElem` all_allowed) attrs
>   in  case (bad_attrs) of
>         [] -> return ()
>         (a:_) -> assertEmptyAttributes errmsg attrs

> reportDuplicateAttributes :: [String] -> Attributes -> SV_Parser ()
> reportDuplicateAttributes allowed_dups attrs =
>     let -- filter out the allowed duplicates
>         getStr a = getIdString (attr_name a)
>         attrs' = filter (\a -> getStr a `notElem` allowed_dups) attrs
>         -- group the remaining attributes
>         groupFunc a1 a2 = (attr_name a1) == (attr_name a2)
>         groups = groupBy groupFunc attrs'
>         -- allow the same attribute twice if the value is the same?
>         groups_nodup = map nub groups
>         -- remove lists of size 1
>         real_groups = filter (\g -> length g > 1) groups_nodup
>     in
>         case (real_groups) of
>           [] -> return ()
>           ((a:_):_) -> let pos = getPosition a
>                            str = getIdString (attr_name a)
>                        in  failWithErr (pos, EMultipleAttribute str)
>           ([]:_) -> internalError "reportDuplicateAttributes"

convert attribute values

> attValue2Bool :: Id -> AttValue -> SV_Parser Bool
> attValue2Bool a (AVNum _ 1)  = return True
> attValue2Bool a (AVNum _ 0)  = return False
> attValue2Bool a value =
>     failWithErr (getPosition value,
>                  EBadAttributeValue (getIdString a) "a Boolean")

> attValue2String :: Id ->  AttValue -> SV_Parser String
> attValue2String _ (AVString _ s) = return s
> attValue2String a (AVList _ ss)  = fmap concat (mapM (attValue2String a) ss)
> attValue2String a value          = failWithErr (getPosition value, EBadAttributeValue (getIdString a) "a string")

> attValue2NonEmptyString :: Id -> AttValue -> SV_Parser String
> attValue2NonEmptyString a (AVString pos "") = failWithErr (pos, EBadAttributeValue (getIdString a) "a non-empty string" )
> attValue2NonEmptyString _ (AVString _ s)    = return s
> attValue2NonEmptyString a v@(AVList _ _)  = do
>                       s <- attValue2String a v
>                       when (s=="") (failWithErr
>                                     (getPosition v, EBadAttributeValue
>                                      (getIdString a) "a non-empty string" ))
>                       return s
> attValue2NonEmptyString a value             =
>     failWithErr (getPosition value, EBadAttributeValue (getIdString a) "a non-empty string" )

process attributes on decls (only keep allowed)

> attributes2keep :: Attributes -> SV_Parser Bool
> attributes2keep attrs = do
>     let allowed = [ "keep" ]
>     _ <- reportBadAttributeName "a declaration" allowed [] attrs
>     _ <- reportDuplicateAttributes [] attrs
>     let processKeep (Attribute name (AVNum _ 1))
>             | getIdString name == "keep" = True
>         processKeep _ = False
>     return (any processKeep attrs)

process attributes attached to a function

> attributes2funcpragma :: Id -> Attributes -> SV_Parser [Pragma]
> attributes2funcpragma funcId attrs = do
>     let allowed = [ "noinline", "options" ]
>         hidden = ["deprecate"]
>     _ <- reportBadAttributeName "a function" allowed hidden attrs
>     _ <- reportDuplicateAttributes [] attrs
>     -- function for reporting an error
>     let err val name expected =
>             let pos = getPosition val
>                 str = getIdString name
>             in  failWithErr (pos, EBadAttributeValue str expected)
>     -- pull out "noinline" and handle separately
>     let (noinline_attrs, pprop_attrs) =
>             partition (\a -> getIdString (attr_name a) == "noinline") attrs
>     -- process "noinline"
>     let numeric a = do b <- attValue2Bool (attr_name a) (attr_value a)
>                        return $ if b
>                                 then Just (Pnoinline [funcId])
>                                 else Nothing
>     noinline_pragma <- mapM numeric noinline_attrs
>     -- process the PProp attributes
>     let strings aname ss [] = return (PPoptions (reverse ss))
>         strings aname ss ((AVString _ s):vs) = strings aname (s:ss) vs
>         strings aname _ (v:ss) = err v aname "a string"
>         stringP p a val = (attValue2String a val) >>= \s -> return (p s)
>     let handlePPropAttr (Attribute name value) =
>             case (getIdString name) of
>               "options" ->
>                  case value of
>                    AVList _ vs  -> strings name [] vs
>                    AVString p s -> strings name [] [value]
>                    _  -> err value name "a string list"
>               "deprecate" -> stringP PPdeprecate name value
>               _ -> internalError "attributes2funcpragma"
>     pps <- mapM handlePPropAttr pprop_attrs
>     let pprop_pragma = if (null pps)
>                        then Nothing
>                        else Just (Pproperties funcId pps)
>     -- return all the pragmas
>     -- XXX warn that option is being ignore if noinline not specified?
>     return (catMaybes (noinline_pragma ++ [pprop_pragma]))


process attributes attached to import-BVI

> attributes2ForeignModPragma :: Id -> Attributes -> SV_Parser [Pragma]
> attributes2ForeignModPragma modId attrs = do
>     let --allowed = []
>         hidden = ["deprecate"]
>         allowed_duplicate = []
>     _ <- reportBadAttributeNameNoAllowed EAttribsForeignModule hidden attrs
>     _ <- reportDuplicateAttributes allowed_duplicate attrs
>     let stringP p a val = (attValue2String a val) >>= \s -> return (p s)
>     let handlePPropAttr (Attribute name value) =
>             case (getIdString name) of
>               "deprecate" -> stringP PPdeprecate name value
>               _ -> internalError "attributes2funcpragma"
>     pps <- mapM handlePPropAttr attrs
>     return $ if (null pps)
>              then []
>              else [Pproperties modId pps]


process attributes attached to a module

> attributes2modpprops :: Attributes -> SV_Parser ([PProp],[CSchedulePragma])
> attributes2modpprops attrs = do
>     let allowed = ["synthesize", "always_ready", "always_enabled",
>                    "clock_prefix", "gate_prefix", "reset_prefix",
>                    "doc", "descending_urgency", "preempts",
>                    "execution_order", "mutually_exclusive", "conflict_free",
>                    "default_clock_osc", "default_clock_gate",
>                    "default_gate_inhigh", "default_gate_unused",
>                    "default_reset", "no_default_clock", "no_default_reset",
>                    "gate_all_clocks", "gate_input_clocks",
>                    "clock_family", "clock_ancestors" ]

hidden attributes are also allowed, but not advertised in
the error message

>         hidden  = ["enabled_when_ready", "bit_blast",
>                    "scan_insert", "options", "deprecate",
>                    "internal_scheduling", "method_scheduling",
>                    "perf_spec" ]
>         -- these will give a warning
>         deprecated = [("CLK", "clock_prefix"),
>                       ("RSTN", "reset_prefix"),
>                       ("RST_N", "reset_prefix")]
>         -- these will give an error
>         obsolete = [("alwaysReady", "always_ready"),
>                     ("alwaysEnabled", "always_enabled"),
>                     ("bitBlast", "bit_blast"),
>                     ("scanInsert", "scan_insert"),
>                     ("verilog", "synthesize")]
>         allowed_duplicate = ["doc", "descending_urgency", "preempts",
>                              "options", "mutually_exclusive",
>                              "conflict_free", "execution_order",
>                              "internal_scheduling", "method_scheduling",
>                              "perf_spec", "gate_input_clocks",
>                              "clock_family", "clock_ancestors"]
>     attrs' <- reportDeprecatedAttributeName deprecated obsolete attrs
>     _ <- reportBadAttributeName "a module" allowed hidden attrs'
>     _ <- reportDuplicateAttributes allowed_duplicate attrs'
>     mprags <- mapM (attribute2modpprop allowed) attrs'
>     let (pprops, sprags) = separate (catMaybes mprags)
>     return (pprops, sprags)

> attribute2modpprop :: [String] -> Attribute ->
>                       SV_Parser (Maybe (Either PProp CSchedulePragma))
> attribute2modpprop allowed attr@(Attribute name value) =
>   -- function for reporting an error
>   let err val name expected =
>           let pos = getPosition val
>               str = getIdString name
>           in  failWithErr (pos, EBadAttributeValue str expected)
>       numeric p a = (attValue2Bool a value) >>= \b -> if b
>                     then return $ Just (Left p)
>                     else return $ Nothing
>       stringP p a = (attValue2String a value) >>= \s ->
>                     return $ Just (Left (p s))
>       nonEmptyStringP p a = (attValue2NonEmptyString a value) >>= \s ->
>                             return $ Just (Left (p s))
>       nonEmptyStringPM f a = (attValue2NonEmptyString a value) >>= \s -> do
>                              pp <- f s
>                              return $ Just (Left pp)
>       nonEmptyStringS f a = (attValue2NonEmptyString a value) >>= \s -> do
>                             sp <- f s
>                             return $ Just (Right sp)
>       strings a ss [] = return $ Just (Left (PPoptions (reverse ss)))
>       strings a ss ((AVString _ s):vs) = strings a (s:ss) vs
>       strings a _ (v:ss) = err v a "a string"
>       -- These now apply to individual components,
>       -- but we keep the numeric for backwards compatibility
>       longnamesOrNumeric f a =
>           case value of
>               -- value of [] means that it applies to whole module
>               AVNum _ 1 -> return $ Just (Left (f []))
>               AVNum _ 0 -> return $ Nothing
>               AVString _ ls -> do
>                   ls' <- string2Longnames (getPosition value) ls
>                   return $ Just (Left (f ls'))
>               _ -> err value a "a string list"
>       mkDef p i s = p [(i,s)]
>       def_clk = setIdPosition (getIdPosition name) idDefaultClock
>       def_rst = setIdPosition (getIdPosition name) idDefaultReset
>   in case getIdString name of
>        "synthesize" -> numeric PPverilog name
>        "always_ready" -> longnamesOrNumeric PPalwaysReady name
>        "always_enabled" -> longnamesOrNumeric PPalwaysEnabled name
>        "enabled_when_ready" -> longnamesOrNumeric PPenabledWhenReady name
>        "bit_blast" -> numeric PPbitBlast name
>        "scan_insert" -> case value of
>                           AVNum _ n -> return $ Just (Left (PPscanInsert n))
>                           _         -> err value name "a number"
>        "clock_prefix" -> stringP PPCLK  name
>        "gate_prefix"  -> stringP PPGATE name
>        "reset_prefix" -> stringP PPRSTN name
>        "default_clock_osc" ->
>            stringP (mkDef PPclock_osc def_clk) name
>        "default_clock_gate" ->
>            nonEmptyStringP (mkDef PPclock_gate def_clk) name
>        "default_gate_inhigh" -> numeric (PPgate_inhigh [def_clk]) name
>        "default_gate_unused" -> numeric (PPgate_unused [def_clk]) name
>        "default_reset" -> stringP (mkDef PPreset_port def_rst) name
>        "no_default_clock" -> numeric (PPclock_osc [(def_clk,"")]) name
>        "no_default_reset" -> numeric (PPreset_port [(def_rst,"")]) name
>        "options" -> case value of
>                         AVList _ vs  -> strings name [] vs
>                         AVString p s -> strings name [] [value]
>                         _ -> err value name "string list"
>        "descending_urgency" ->
>            nonEmptyStringS (psUrgency (getPosition value)) name
>        "execution_order" ->
>            nonEmptyStringS (psExecutionOrder (getPosition value)) name
>        "mutually_exclusive" ->
>            nonEmptyStringS (psMutuallyExclusive (getPosition value)) name
>        "conflict_free" ->
>            nonEmptyStringS (psConflictFree (getPosition value)) name
>        "internal_scheduling" ->
>            nonEmptyStringS (psScheduling False (getPosition value)) name
>        "method_scheduling" ->
>            let f (SPSchedule mci) = PPmethod_scheduling mci
>                f _ = internalError "attributes2modpprops: method_scheduling"
>            in nonEmptyStringPM
>                   ((fmap f).(psScheduling False (getPosition value))) name
>        "preempts" ->
>            nonEmptyStringS (psScheduling True  (getPosition value)) name
>        --"clocked_by" ->
>        --    nonEmptyStringPM (psClockedBy (getPosition value)) name
>        "doc" -> stringP (PPdoc) name
>        "deprecate" -> stringP (PPdeprecate) name
>        "perf_spec" -> nonEmptyStringPM (psPerfSpec (getPosition value)) name
>        "gate_all_clocks" -> numeric (PPgate_input_clocks []) name
>        "gate_input_clocks" ->
>            nonEmptyStringPM (psInputClocks (getPosition value)) name
>        "clock_family" ->
>            nonEmptyStringPM (psClockFamily (getPosition value)) name
>        "clock_ancestors" ->
>            nonEmptyStringPM (psClockAncestors (getPosition value)) name
>        -- this shouldn't happen if the lists are kept in sync
>        str -> failWithErr (getPosition value,
>                            EBadAttributeName str "a module" allowed)

convert attributes to rule pragmas

> attributes2rprags :: Attributes -> SV_Parser ([RulePragma],[CSchedulePragma])
> attributes2rprags attrs = do
>     let -- only the following are visible to the user
>         allowed = ["descending_urgency", "execution_order",
>                    "doc", "fire_when_enabled",
>                    "no_implicit_conditions", "preempts",
>                    "mutually_exclusive", "conflict_free"]
>         hidden = ["aggressive_implicit_conditions", "conservative_implicit_conditions",
>                   "no_warn", "warn_all_conflicts",
>                   "can_schedule_first", "clock_crossing_rule", "hide"]
>         deprecated = []
>         obsolete = []
>         allowed_duplicate = ["descending_urgency", "execution_order",
>                              "doc", "preempts",
>                              "mutually_exclusive", "conflict_free"]
>     attrs' <- reportDeprecatedAttributeName deprecated obsolete attrs
>     _ <- reportBadAttributeName "a rule" allowed hidden attrs'
>     _ <- reportDuplicateAttributes allowed_duplicate attrs'
>     mprags <- mapM (attribute2rprag allowed) attrs'
>     let (rprags, sprags) = separate (catMaybes mprags)
>     return (rprags, sprags)

> attribute2rprag :: [String] -> Attribute ->
>                    SV_Parser (Maybe (Either RulePragma CSchedulePragma))
> attribute2rprag allowed attr@(Attribute name value) =
>   let numeric p a = do b <- attValue2Bool a value
>                        return $ if b
>                                 then Just (Left p)
>                                 else Nothing
>       nonEmptyStringS f a =
>           do s <- attValue2NonEmptyString a value
>              rp <- f s
>              return $ Just (Right rp)
>       stringP p a = do s <- attValue2String a value
>                        return $ Just (Left (p s))
>   in case getIdString name of
>          "fire_when_enabled" -> numeric RPfireWhenEnabled name
>          "no_implicit_conditions" -> numeric RPnoImplicitConditions name
>          "can_schedule_first" -> numeric RPcanScheduleFirst name
>          "clock_crossing_rule" -> numeric RPclockCrossingRule name
>          "descending_urgency" ->
>              nonEmptyStringS (psUrgency (getPosition value)) name
>          "execution_order" ->
>              nonEmptyStringS (psExecutionOrder (getPosition value)) name
>          "mutually_exclusive" ->
>              nonEmptyStringS (psMutuallyExclusive (getPosition value)) name
>          "conflict_free" ->
>              nonEmptyStringS (psConflictFree (getPosition value)) name
>          "preempts" ->
>              nonEmptyStringS (psScheduling True  (getPosition value)) name
>          "aggressive_implicit_conditions" ->
>              numeric RPaggressiveImplicitConditions name
>          "conservative_implicit_conditions" ->
>              numeric RPconservativeImplicitConditions name
>          "doc"                -> stringP RPdoc name
>          "hide"               -> numeric RPhide name
>          "no_warn"            -> numeric RPnoWarn name
>          "warn_all_conflicts" -> numeric RPwarnAllConflicts name
>          -- this shouldn't happen if the lists are kept in sync
>          str -> failWithErr (getPosition value,
>                              EBadAttributeName str "a rule" allowed)

convert attributes to instantiation properties

> attributes2instpprops :: Attributes -> SV_Parser [(Position, PProp)]
> attributes2instpprops = attributes2instpprops' []

> attributes2instpprops' :: [(Position,PProp)] -> Attributes ->
>                           SV_Parser [(Position, PProp)]
> attributes2instpprops' sofar [] = return (reverse sofar)
> attributes2instpprops' sofar (attr@(Attribute name value):rest) =
>   let pos = getPosition name
>       stringP p a = (attValue2String a value) >>= \s ->
>                   attributes2instpprops' ((pos, p s):sofar) rest
>       idP p a = (attValue2String a value) >>= \s ->
>                   attributes2instpprops' ((pos, p (mk_dangling_id s pos)):sofar) rest
>       jP p    = attributes2instpprops' ((pos, p):sofar) rest
>       allowed = ["doc"]
>   in  case getIdString name of
>           "doc"        -> stringP (PPdoc) name
>           "inst_name"  -> idP (PPinst_name) name
>           "hide"  -> jP (PPinst_hide)
>           "hide_all"  -> jP (PPinst_hide_all)
>           str   -> failWithErr (getPosition value, EBadAttributeName str "an instantiation" allowed)

 bool pair give scope information -- module scope, method pragma

> attributes2IfcPragmas :: (Bool,Bool) -> Attributes -> SV_Parser [IfcPragma]
> attributes2IfcPragmas _ [] = return []
> attributes2IfcPragmas (fullifc,ismethod) attrs = attributes2IfcPragmas'  [] attrs
>     where attributes2IfcPragmas' ::  [IfcPragma] -> Attributes -> SV_Parser [IfcPragma]
>           attributes2IfcPragmas' collection [] = return collection
>           attributes2IfcPragmas' collection (this@(Attribute id attval) : rest) =
>               do let pos = getPosition attval
>                  newprag <- case (fullifc, ismethod,getIdString id) of
>                             (False,_,"prefix")         -> attValue2String id attval >>= checkIfcPragma (pos,"prefix",True) >>=
>                                                               (\s -> return (PIPrefixStr s) )
>                             (False,True,"ready")       -> attValue2String id attval >>= checkIfcPragma (pos,"ready",False) >>=
>                                                               (\s -> return (PIRdySignalName s ) )
>                             (False,True,"enable")      -> attValue2String id attval >>= checkIfcPragma (pos,"enable",False) >>=
>                                                               (\s -> return (PIEnSignalName s ) )
>                             (False,True,"result")      -> attValue2String id attval >>= checkIfcPragma (pos,"result",False) >>=
>                                                               (\s -> return (PIResultName s ) )
>                             (False,_,"always_ready")   -> checkNoPragmaArg attval id PIAlwaysRdy
>                             (False,_,"always_enabled") -> checkNoPragmaArg attval id PIAlwaysEnabled
>                             (True,_,"always_ready")    -> checkNoPragmaArg attval id PIAlwaysRdy
>                             (True,_,"always_enabled")  -> checkNoPragmaArg attval id PIAlwaysEnabled
>                             _                          -> failWithErr (pos, EBadAttributeName (getIdString id) ifcOrmethod allowed)
>

>                  attributes2IfcPragmas' (newprag:collection) rest
>           --
>           ifcOrmethod = if fullifc then "an interface" else if ismethod then "a method" else "a sub-interface"
>           allowed = if ( fullifc) then
>                         ["always_ready", "always_enabled"]
>                     else if ismethod then
>                              ["prefix", "ready", "enable", "result", "always_ready", "always_enabled"]
>                     else -- sub interface
>                     ["prefix", "always_ready", "always_enabled"]
>

Handle port/parameter attributes associated with module arguments.
This returns pragmas with empty identifiers.  The identifiers
are later replaced by the associated argument ids once they
are known.

> handleModuleArgAttrs :: Attributes -> SV_Parser [PProp]
> handleModuleArgAttrs []                     = return []
> handleModuleArgAttrs ((Attribute i v):rest) =
>     do let pos = getPosition v
>            allowed = [ "osc", "gate", "gate_inhigh", "gate_unused",
>                        "reset", "port", "clocked_by" ]
>        pp <- case (getIdString i) of
>                "osc"         -> do s <- attValue2NonEmptyString i v
>                                    return $ PPclock_osc [(emptyId,s)]
>                "gate"        -> do s <- attValue2NonEmptyString i v
>                                    return $ PPclock_gate [(emptyId,s)]
>                "gate_inhigh" -> return $ PPgate_inhigh [emptyId]
>                "gate_unused" -> return $ PPgate_unused [emptyId]
>                "reset"       -> do s <- attValue2NonEmptyString i v
>                                    return $ PPreset_port [(emptyId,s)]
>                "port"        -> do s <- attValue2NonEmptyString i v
>                                    return $ PParg_port [(emptyId,s)]
>                "clocked_by"  -> do s <- attValue2NonEmptyString i v
>                                    return $ PParg_clocked_by [(emptyId,s)]
>                "reset_by"    -> do s <- attValue2NonEmptyString i v
>                                    return $ PParg_reset_by [(emptyId,s)]
>                attr          -> failWithErr (pos,  EBadAttributeName attr "a module argument" allowed)
>        remaining_pps <- handleModuleArgAttrs rest
>        return (pp:remaining_pps)
>
> handleModuleParamAttrs :: Attributes -> SV_Parser [PProp]
> handleModuleParamAttrs []                     = return []
> handleModuleParamAttrs ((Attribute i v):rest) =
>     do let pos = getPosition v
>            allowed = [ "parameter" ]
>        pp <- case (getIdString i) of
>                "parameter"   -> do s <- attValue2NonEmptyString i v
>                                    return $ PParg_param [(emptyId,s)]
>                attr          -> failWithErr (pos,  EBadAttributeName attr "a module parameter" allowed)
>        remaining_pps <- handleModuleArgAttrs rest
>        return (pp:remaining_pps)

> best :: Id -> Id -> Id
> best i x = if (x == emptyId) then i else x
>
> addPragmaId :: Id -> PProp -> PProp
> addPragmaId n (PPclock_osc ps)   = PPclock_osc  [(best n i, s) | (i,s) <- ps]
> addPragmaId n (PPclock_gate ps)  = PPclock_gate [(best n i, s) | (i,s) <- ps]
> addPragmaId n (PPgate_inhigh is) = PPgate_inhigh (map (best n) is)
> addPragmaId n (PPgate_unused is) = PPgate_unused (map (best n) is)
> addPragmaId n (PPreset_port ps)  = PPreset_port [(best n i, s) | (i,s) <- ps]
> addPragmaId n (PParg_param ps)   = PParg_param  [(best n i, s) | (i,s) <- ps]
> addPragmaId n (PParg_port ps)    = PParg_port   [(best n i, s) | (i,s) <- ps]
> addPragmaId n (PParg_clocked_by ps) = PParg_clocked_by (mapFst (best n) ps)
> addPragmaId n (PParg_reset_by ps) = PParg_reset_by (mapFst (best n) ps)
> addPragmaId _ pp                 = pp

Handle port attributes associated with a function/method argument.

> attributes2PortName :: Attributes -> SV_Parser (Maybe String)
> attributes2PortName []  =  return Nothing
> attributes2PortName as = attributes2PortName' Nothing as
>     where attributes2PortName' :: Maybe String -> Attributes -> SV_Parser (Maybe String)
>           attributes2PortName' ms []                                  = return ms
>           attributes2PortName' ms (this@(Attribute id attval) : rest) = do
>               let pos = getPosition attval
>               newprag <- case ( ms, getIdString id) of
>                          (Nothing, "port" ) ->  attValue2String  id attval >>= checkIfcPragma (pos,"port",False) >>=
>                                                        (\s -> return $ Just s)
>                          (Just s, "port")   -> failWithErr (pos, EMultipleAttribute "port")
>                          (_, _)             -> failWithErr (pos, EBadAttributeName (getIdString id) "a function argument" allowed)
>                                                     where
>                                                     allowed = ["port"]
>               attributes2PortName' newprag rest
>
> checkIfcPragma :: (Position,String,Bool) -> String -> SV_Parser String
> checkIfcPragma (pos, attrname, emptyAllowed) str =
>     case isValid of
>        True -> return str
>        False -> failWithErr (pos, EBadPortRenameAttributeString attrname str)
>     where isValid = (emptyAllowed || not (null str)) && not (any isWhitespace str)

> checkNoPragmaArg :: AttValue -> Id -> a -> SV_Parser a
> checkNoPragmaArg (AVNum _ 1) _ x = return x
> checkNoPragmaArg attv  attrid _  = failWithErr ( getPosition attv, EAttributeArgNotAllowed (getIdString attrid))

> pAttributeWithParser :: SV_Parser a -> Position -> String -> SV_Parser a
> pAttributeWithParser pragmaParser pos s =
>  do
>    errh <- getErrHandle
>    pFlags <- getParserFlags
>    ioToParser $ do
>       let startPos = updatePosChar pos '\"'
>           tokens = scan startPos s
>       result <- runParser pragmaParser (emptyParserState errh pFlags)
>                                          startPos tokens
>       case result of
>          Left  errs -> bsError errh errs
>          Right prs  -> return prs

Convert argument strings of attributes to CSchedulePragmas etc.

> {-
> psClockedBy :: Position -> String -> SV_Parser PProp
> psClockedBy p s =
>  do let pPair = pInParens ( do i1 <- pCompoundIdentifier
>                                pSymbol SV_SYM_comma
>                                i2 <- pCompoundIdentifier
>                                return (i1,i2) )
>         pClocked = do prs <- many1 pPair
>                       eof svTokenToString <?> "end of string"
>                       return prs
>     PPclocked_by <$> pAttributeWithParser pClocked p s
> -}

> psInputClocks :: Position -> String -> SV_Parser PProp
> psInputClocks p s =
>  do let pInp = do lns <- pCommaSep1 pIdentifier
>                   eof svTokenToString <?> "end of string"
>                   return lns
>     PPgate_input_clocks <$> pAttributeWithParser pInp p s

> psUrgency :: Position -> String -> SV_Parser CSchedulePragma
> psUrgency p s = SPUrgency <$> string2Longnames p s

> psExecutionOrder :: Position -> String -> SV_Parser CSchedulePragma
> psExecutionOrder p s = SPExecutionOrder <$> string2Longnames p s

> psMutuallyExclusive :: Position -> String -> SV_Parser CSchedulePragma
> psMutuallyExclusive p s =
>  do let pME  = do lns <- pCommaSep1 pGroup
>                   eof svTokenToString <?> "end of string"
>                   return lns
>     SPMutuallyExclusive <$> pAttributeWithParser pME p s

> psConflictFree :: Position -> String -> SV_Parser CSchedulePragma
> psConflictFree p s =
>  do let pCF  = do lns <- pCommaSep1 pGroup
>                   eof svTokenToString <?> "end of string"
>                   return lns
>     SPConflictFree <$> pAttributeWithParser pCF p s

> string2Longnames :: Position -> String -> SV_Parser [Longname]
> string2Longnames p s =
>  do let pLN  = do lns <- pLongnames
>                   eof svTokenToString <?> "end of string"
>                   return lns
>     pAttributeWithParser pLN p s

> psScheduling :: Bool -> Position -> String -> SV_Parser CSchedulePragma
> psScheduling doingPreempts p s =
>  do let pInside = do els <- (if doingPreempts
>                              then (fmap (:[])) else many1)
>                                 (pMethodConflict doingPreempts)
>                      eof svTokenToString <?> "end of string"
>                      return els
>     result <- pAttributeWithParser pInside p s
>     return (if doingPreempts
>             then case result of
>                    [(is1,_,is2)] -> SPPreempt is1 is2
>                    _ -> internalError "psScheduling: unexpected preempts result"
>             else SPSchedule (mkMethodConflictInfo result))

> psPerfSpec :: Position -> String -> SV_Parser PProp
> psPerfSpec pos str =
>   do let pPSpec  =  (pInBrackets (pCommaSep pIdentifier))
>                 <|> ((:[]) <$> pIdentifier)
>          pPSpecs = do ranks <- pPSpec `sepBy` pSymbol SV_SYM_lt
>                       eof svTokenToString <?> "end of string"
>                       return ranks
>      spec <- pAttributeWithParser pPSpecs pos str
>      return (PPperf_spec spec)

> psClockFamily :: Position -> String -> SV_Parser PProp
> psClockFamily p s =
>  do let pClockName = pIdentifier <?> "clock name"
>         pInp = do lns <- pCommaSep1 pClockName
>                   eof svTokenToString <?> "end of string"
>                   return lns
>     PPclock_family <$> pAttributeWithParser pInp p s

> psClockAncestors :: Position -> String -> SV_Parser PProp
> psClockAncestors p s =
>  do let pClockName = pIdentifier <?> "clock name"
>         pASeq = do x <- pClockName
>                    pTheString "AOF"
>                    rest <- sepBy1 pClockName (pTheString "AOF")
>                    return (x:rest)
>         pInp  = do lns <- pCommaSep1 pASeq
>                    eof svTokenToString <?> "end of string"
>                    return lns
>     PPclock_ancestors <$> pAttributeWithParser pInp p s

=========

ASSERTIONS

What follows is the code to handle parsing System Verilog Assertions (SVA).

The abstract syntax is defined in CVParserImperative.lhs

> pExprSeq :: SV_Parser CExpr
> pExprSeq = pExpression

The following is a more restricted form, very strongly binding on its left,
and eschewing all forms which couldn't possibly have the right type.

> pDelayExpr :: SV_Parser CExpr
> pDelayExpr
>    =  (     -- XXX This accepts signed numbers, '1, '0, etc
>             pNumericLiteral
>        <|> (pInParens pExpression)
>        <|> (fmap CVar pIdentifier)
>        <?> "Delay expression")


> pSPExpr :: SV_Parser SVA_SP
> pSPExpr = buildExpressionParser seqpropTable pSPTerm
> pSPExprInIf :: SV_Parser SVA_SP
> pSPExprInIf = buildExpressionParser seqpropTable2 pSPTerm


> seqpropTable :: OperatorTable SV_Token SV_Parser_State SVA_SP
> seqpropTable =
>  [[prefixOpP     SV_SYM_hash_hash  (SVA_SP_DelayU)     AssocLeft],
>   [binOpP        SV_SYM_hash_hash  (SVA_SP_Delay)      AssocLeft],
>   [binOp         SV_KW_throughout  (SVA_SP_Throughout) AssocRight],
>   [binOp         SV_KW_within      (SVA_SP_Within)     AssocLeft],
>   [binOp         SV_KW_intersect   (SVA_SP_Intersect)  AssocLeft],
>   [prefixOp      SV_KW_not         (SVA_SP_Not)                      ],
>   [binOp         SV_KW_and         (SVA_SP_And)        AssocLeft],
>   [binOp         SV_KW_or          (SVA_SP_Or)         AssocLeft],
>   [binOpS        SV_SYM_pipe_minus_gt (SVA_SP_Implies) AssocRight],
>   [binOpS        SV_SYM_pipe_eq_gt (SVA_SP_ImpliesD)   AssocRight]]
>  where
>   prefixOp kw fun = Prefix (do{ pKeyword kw; return fun})
>   binOp    kw fun assoc = Infix (do{ pKeyword kw; return fun }) assoc
>   binOpS  sym fun assoc = Infix (do{ pSymbol sym; return fun }) assoc
>   binOpP  sym fun assoc = Infix (do{ pSymbol sym; dr <- pHashDelay; rest <- many pDelaySeq; return (fun dr rest)}) assoc
>   prefixOpP sym fun assoc = Prefix (do{ pSymbol sym; dr <- pHashDelay; rest <- many pDelaySeq; return (fun dr rest)})

> seqpropTable2 :: OperatorTable SV_Token SV_Parser_State SVA_SP
> seqpropTable2 =
>  [[prefixOpP     SV_SYM_hash_hash  (SVA_SP_DelayU)     AssocLeft],
>   [binOpP        SV_SYM_hash_hash  (SVA_SP_Delay)      AssocLeft],
>   [binOp         SV_KW_throughout  (SVA_SP_Throughout) AssocRight],
>   [binOp         SV_KW_within      (SVA_SP_Within)     AssocLeft],
>   [binOp         SV_KW_intersect   (SVA_SP_Intersect)  AssocLeft],
>   [prefixOp      SV_KW_not         (SVA_SP_Not)                      ],
>   [binOp         SV_KW_and         (SVA_SP_And)        AssocLeft],
>   [binOp         SV_KW_or          (SVA_SP_Or)         AssocLeft]]
>  where
>   prefixOp kw fun = Prefix (do{ pKeyword kw; return fun})
>   binOp    kw fun assoc = Infix (do{ pKeyword kw; return fun }) assoc
>   binOpP  sym fun assoc = Infix (do{ pSymbol sym; dr <- pHashDelay; rest <- many pDelaySeq; return (fun dr rest)}) assoc
>   prefixOpP sym fun assoc = Prefix (do{ pSymbol sym; dr <- pHashDelay; rest <- many pDelaySeq; return (fun dr rest)})

> pDelaySeq :: SV_Parser SVA_SP
> pDelaySeq =
>  do
>   pSymbol SV_SYM_hash_hash
>   dr <- pDelayRange
>   se <- pSPExpr
>   return (SVA_SP_DelayU dr [] se)

> pSPTerm :: SV_Parser SVA_SP
> pSPTerm =
>    pMatchItem
>    <|> pFirstMatch
>    <|> pSPIf
>    <|> try pSPItem
>    <|> pInParens pSPExpr

> pFirstMatch :: SV_Parser SVA_SP
> pFirstMatch =
>  do
>   pos <- getPos
>   pKeyword SV_KW_first_match
>   (SVA_SP_Match sq asgns rep) <- pMatchItem
>   return (SVA_SP_FirstMatch sq asgns rep)

> pSPItem :: SV_Parser SVA_SP
> pSPItem =
>  do
>   exp <- pExprSeq
>   rep <- pBoolAbbrev
>   return (SVA_SP_Expr exp rep)

> pMatchItem :: SV_Parser SVA_SP
> pMatchItem = try $
>   do
>    pSymbol SV_SYM_lparen
>    sq <- pSPExpr
>    asgns <- {-option []-} pMatchItems
>    pSymbol SV_SYM_rparen
>    rep <- pBoolAbbrev
>    return ({-if null asgns then SVA_SP_Parens sq rep
>                          else-} SVA_SP_Match sq asgns rep)

> pMatchItems :: SV_Parser [[ImperativeStatement]]
> pMatchItems =
>  do
>   pSymbol SV_SYM_comma
>   let seqMatchFlags = nullImperativeFlags {allowEq = True}
>   pCommaSep (pImperativeDeclOrAssign [] seqMatchFlags False)

> pSPIf :: SV_Parser SVA_SP
> pSPIf =
>  do
>   pKeyword SV_KW_if
>   e <- pInParens pExprSeq
>   p1 <- pSPExprInIf
>   p2 <- option (Nothing) pSPElse
>   return (SVA_SP_If e p1 p2)

> pSPElse :: SV_Parser (Maybe SVA_SP)
> pSPElse =
>  do
>   pKeyword SV_KW_else
>   p <- pSPExprInIf
>   return (Just p)

> pBoolAbbrev :: SV_Parser (SVA_REP)
> pBoolAbbrev =
>   pConsRep
>   <|> pNonConsRep
>   <|> pGotoRep
>   <|> return (SVA_REP_None)

> pConsRep :: SV_Parser SVA_REP
> pConsRep =
>  do
>   pSymbol SV_SYM_lbracket_star
>   r <- pDelayRange
>   pSymbol SV_SYM_rbracket
>   return (SVA_REP_Cons r)

> pNonConsRep :: SV_Parser SVA_REP
> pNonConsRep =
>  do
>   pSymbol SV_SYM_lbracket_eq
>   r <- pDelayRange
>   pSymbol SV_SYM_rbracket
>   return (SVA_REP_NonCons r)

> pGotoRep :: SV_Parser SVA_REP
> pGotoRep =
>  do
>   pSymbol SV_SYM_lbracket_minus_gt
>   r <- pDelayRange
>   pSymbol SV_SYM_rbracket
>   return (SVA_REP_Goto r)

> pHashDelay :: SV_Parser SVA_Delay
> pHashDelay =
>  SVA_Delay_Const <$> pDelayExpr
>   <|> (do
>         pSymbol SV_SYM_lbracket
>         res <- pDelayRange -- XXX Delay_const should not be allowed here
>         pSymbol SV_SYM_rbracket
>         return res)

> pDelayRange :: SV_Parser SVA_Delay
> pDelayRange =
>  do
>   e <- pDelayExpr
>   option (SVA_Delay_Const e) (pRangeEnd e)

> pRangeEnd :: CExpr -> SV_Parser SVA_Delay
> pRangeEnd e =
>  do
>    pSymbol SV_SYM_colon
>    pRangeUnbound <|> pRangeBound
>  where
>   pRangeUnbound = do
>             pDollar
>             return (SVA_Delay_Unbound e)
>   pRangeBound = SVA_Delay_Range e <$> pDelayExpr

SEQUENCES

> pSequence :: Attributes -> ImperativeFlags -> SV_Parser [ImperativeStatement]
> pSequence atts flags =
>  do
>   pos <- getPos
>   pKeyword SV_KW_sequence <?> "sequence"
>   ignoreAssertions <- disableAssertions <$> getParserFlags
>   when (not ignoreAssertions) (parseWarn (pos, WExperimental "SV assertions"))
>   when (not (allowSequence flags))
>        (failWithErr (pos, EForbiddenSequenceDecl (pvpString (stmtContext flags)) ""))
>   assertEmptyAttributes EAttribsSequence atts
>   name <- pIdentifier <?> "sequence name"
>   args <- option [] (pInParens (pCommaSep pFunctionArgOptType)) <?> "sequence arguments"
>   context <- option [] pProvisos
>   pSemi
>   let seqMatchFlags = nullImperativeFlags {allowAssertVar = True}
>   vars <- many (try (pImperativeDeclOrAssignSemi [] seqMatchFlags))
>   body <- pSPExpr
>   pSemi
>   pEndClause SV_KW_endsequence (Just name)
>   pFlags <- getParserFlags
>   let res = if (disableAssertions pFlags)
>              then [ISDecl pos (Right name) Nothing []]
>              else [ISSequence pos (name, args, context, vars, body)]
>   return res

PROPERTIES

> pProperty :: Attributes -> ImperativeFlags -> SV_Parser [ImperativeStatement]
> pProperty atts flags =
>  do
>   pos <- getPos
>   pKeyword SV_KW_property <?> "property declaration"
>   ignoreAssertions <- disableAssertions <$> getParserFlags
>   when (not ignoreAssertions) (parseWarn (pos, WExperimental "SV assertions"))
>   when (not (allowProperty flags))
>        (failWithErr (pos, EForbiddenPropertyDecl (pvpString (stmtContext flags)) ""))
>   assertEmptyAttributes EAttribsProperty atts
>   name <- pIdentifier <?> "property name"
>   args <- option [] (pInParens (pCommaSep pFunctionArgOptType)) <?> "property arguments"
>   context <- option [] pProvisos
>   pSemi
>   let seqMatchFlags = nullImperativeFlags {allowAssertVar = True}
>   vars <- option [] (try (many1 (try (pImperativeDeclOrAssignSemi [] seqMatchFlags))))
>   body <- pSPExpr
>   pSemi
>   pEndClause SV_KW_endproperty (Just name)
>   pFlags <- getParserFlags
>   let res = if (disableAssertions pFlags)
>              then [ISDecl pos (Right name) Nothing []]
>              else [ISProperty pos (name, args, context, vars, body)]
>   return res

ASSERTIONS

> pAssertion :: Attributes -> ImperativeFlags -> SV_Parser [ImperativeStatement]
> pAssertion atts flags = pAssertion1 Nothing atts flags

> pAssertionWithLabel :: Attributes -> ImperativeFlags -> SV_Parser [ImperativeStatement]
> pAssertionWithLabel atts flags =
>  do
>    pos <- getPos
>    label <- try (do
>                   id <- pIdentifier
>                   pColon
>                   return id)
>    let ctxt = stmtContext flags
>    if (ctxt == ISCSequence) then (pImperativeLabel pos label atts flags) else (pAssertion1 (Just label) atts flags)

> pAssertion1 :: (Maybe Id) -> Attributes -> ImperativeFlags -> SV_Parser [ImperativeStatement]
> pAssertion1 mid atts flags =
>  do
>    pos <- getPos
>    always <- option (True) (pInitialStmt <|> pAlwaysStmt)
>    st <- pAssertStmt mid atts flags <?> "assertion statement"
>    pFlags <- getParserFlags
>    let res = if (disableAssertions pFlags)
>              then []
>              else [ISAssertStmt pos (always, st)]
>    return res

> pInitialStmt :: SV_Parser Bool
> pInitialStmt =
>  do
>    pKeyword SV_KW_initial
>    return False

> pAlwaysStmt :: SV_Parser Bool
> pAlwaysStmt =
>  do
>    pKeyword SV_KW_always
>    return True

> pAssertStmt :: Maybe Id -> Attributes -> ImperativeFlags -> SV_Parser SVA_STMT
> pAssertStmt mid atts flags =
>    pAssert mid atts flags
>    <|> pAssume mid atts flags
>    <|> pCover mid atts flags
>    <|> pExpect mid atts flags

> pAssert :: Maybe Id -> Attributes -> ImperativeFlags -> SV_Parser SVA_STMT
> pAssert mid atts flags =
>  do
>    pos <- getPos
>    pKeyword SV_KW_assert
>    when (not (allowAssert flags))
>        (failWithErr (pos, EForbiddenAssert (pvpString (stmtContext flags))))
>    ignoreAssertions <- disableAssertions <$> getParserFlags
>    when (not ignoreAssertions) (parseWarn (pos, WExperimental "SV assertions"))
>    assertEmptyAttributes EAttribsAssert atts
>    pKeyword SV_KW_property
>    prop <- pInParens pSPExpr
>    (pass, fail) <- do {pSemi; return ([],[])}
>                    <|> pNakedElse flags
>                   <|> pPassThrough flags
>    return (SVA_STMT_Assert mid prop pass fail)

> pAssume :: Maybe Id -> Attributes -> ImperativeFlags -> SV_Parser SVA_STMT
> pAssume mid atts flags =
>  do
>    pos <- getPos
>    pKeyword SV_KW_assume
>    when (not (allowAssume flags))
>        (failWithErr (pos, EForbiddenAssume (pvpString (stmtContext flags))))
>    ignoreAssertions <- disableAssertions <$>  getParserFlags
>    when (not ignoreAssertions) (parseWarn (pos, WExperimental "SV assertions"))
>    assertEmptyAttributes EAttribsAssume atts
>    pKeyword SV_KW_property
>    prop <- pInParens pSPExpr
>    pSemi
>    return (SVA_STMT_Assume mid prop)

> pCover :: Maybe Id -> Attributes -> ImperativeFlags -> SV_Parser SVA_STMT
> pCover mid atts flags =
>   do
>     pos <- getPos
>     pKeyword SV_KW_cover
>     when (not (allowCover flags))
>        (failWithErr (pos, EForbiddenCover (pvpString (stmtContext flags))))
>     ignoreAssertions <- disableAssertions <$> getParserFlags
>     when (not ignoreAssertions)
>              (parseWarn (pos, WExperimental "SV assertions"))
>     assertEmptyAttributes EAttribsCover atts
>     pKeyword SV_KW_property
>     prop <- pInParens pSPExpr
>     pass <- do {pSemi; return []}
>             <|> pImperativeStmt assertFlags
>     return (SVA_STMT_Cover mid prop pass)

> pExpect :: Maybe Id -> Attributes -> ImperativeFlags -> SV_Parser SVA_STMT
> pExpect mid atts flags =
>   do
>     pos <- getPos
>     pKeyword SV_KW_expect
>     when (not (allowExpect flags))
>        (failWithErr (pos, EForbiddenExpect (pvpString (stmtContext flags))))
>     ignoreAssertions <- disableAssertions <$> getParserFlags
>     when (not ignoreAssertions)
>              (parseWarn (pos, WExperimental "SV assertions"))
>     assertEmptyAttributes EAttribsExpect atts
>     prop <- pInParens pSPExpr
>     (pass, fail) <- do {pSemi; return ([], [])}
>                    <|> pNakedElse flags
>                   <|> pPassThrough flags
>     return (SVA_STMT_Expect mid prop pass fail)

> pNakedElse :: ImperativeFlags
>            -> SV_Parser ([ImperativeStatement],[ImperativeStatement])
> pNakedElse flags =
>  do
>    pKeyword SV_KW_else
>    f <- pImperativeStmt assertFlags
>    return ([], f)
>
> pPassThrough :: ImperativeFlags
>              -> SV_Parser ([ImperativeStatement],[ImperativeStatement])
> pPassThrough flags =
>  do
>    p <- pImperativeStmt actionFlags
>    f <- option [] (pKeyword SV_KW_else >> pImperativeStmt actionFlags)
>    return (p, f)

> assertFlags :: ImperativeFlags
> assertFlags = nullImperativeFlags
>  {
>   stmtContext = ISCExpression,
>   allowEq = True,
>   allowSubscriptAssign = True,
>   allowFieldAssign = True,
>   allowArrayDecl = True,
>   allowBind = True,
>   allowLoops = True,
>   allowConditionals = True,
>   allowNakedExpr = True,
>   allowLet = True
>  }

=========

UTILITIES

get current "Position"

> getPos :: SV_Parser Position
> getPos = Parsec.getPosition

parse tokens into CSyntax

> bsvParseTokens :: ErrorHandle -> Flags ->
>                   Bool -> String -> String -> [SV_Token] ->
>                   IO CPackage
> bsvParseTokens errh flags show_warns filename defaultPkgName tokens =
>     do let initPos | null tokens = initialPosition filename
>                    | otherwise = start_position (head tokens)
>        result <- runParser (pPackageWithWarnings defaultPkgName)
>                  (emptyParserState errh flags) initPos tokens
>        case result of
>          Left  errs         -> bsError errh errs
>          Right (pkg, warns) -> do when (not (null warns) && show_warns) $
>                                       bsWarning errh warns
>                                   return pkg

tokenize and parse string into CSyntax

> bsvParseString :: ErrorHandle -> Flags ->
>                   Bool -> String -> String -> String ->
>                   IO (CPackage, TimeInfo)
> bsvParseString errh flags show_warns filename defaultPkgName source =
>     do
>       let initpos =
>               updatePosStdlib (initialPosition filename) (stdlibNames flags)
>       t <- getNow
>       start flags DFvpp
>       vppOut@(ppsource, includes)  <- preprocess errh flags initpos source
>       let dumpnames = (baseName (dropSuf filename), "", "")
>       t <- dump errh flags t DFvpp dumpnames (VPPOut vppOut)
>       when ( preprocessOnly flags ) $ do putStrLn ppsource
>                                          exitOK errh
>
>       start flags DFbsvlex
>       let tokens = scan initpos ppsource
>       t <- dump errh flags t DFbsvlex dumpnames tokens

parsing is done after we return

>       start flags DFparsed
>       (CPackage name exports imports impsigs fixs defs _)
>            <- bsvParseTokens errh flags show_warns filename defaultPkgName tokens
>       let package = (CPackage name exports imports impsigs fixs defs (map CInclude includes))
>       t <- vdump errh flags t DFparsed dumpnames package
>       return (package, t)

wrapper function to allow parsing from TCL for a specific type
XXX should fixup positions here

> pStringWrapper :: ErrorHandle -> Flags ->
>                   (SV_Parser a) -> [String]  -> IO (Either [EMsg] a)
> pStringWrapper errh flags pf srcs = do
>   let initPos = initialPosition "Commandline"
>       tokens = scan initPos (unwords srcs)
>   runParser wrapped (emptyParserState errh flags) initPos tokens
>       where -- wrapped :: (SV_Parser a)
>             wrapped = do
>                       res <- pf
>                       eof svTokenToString
>                       return res
>
