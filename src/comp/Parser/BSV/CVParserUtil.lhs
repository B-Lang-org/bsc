> module Parser.BSV.CVParserUtil where

> import Parsec
> import Parser.BSV.CVParserCommon

parse multiple 'parser's.  each time, try parsing 'terminator' first; if
it parses, rewind to before the terminator and return the list so far

> manyStopAt :: Parser trm -> Parser val -> Parser [val]
> manyStopAt terminator parser =
>         do tokens <- getInput
>            _ <- terminator
>            setInput tokens
>            return []
>     <|> do val <- parser
>            vals <- manyStopAt terminator parser
>            return (val:vals)

> stmtsAreNonMonadic :: [ImperativeStatement] -> Bool
> stmtsAreNonMonadic = all stmtIsNonMonadic

> stmtIsNonMonadic :: ImperativeStatement -> Bool
> stmtIsNonMonadic stmt =
>     case stmt of
>                ISDecl _ _ _ _ -> True
>                ISPatEq _ _ _ ->  True
>                ISEqual _ _ _ -> True
>                ISUpdate _ _ _ -> True
>                ISFunction _ _ _ -> True
>                ISFor _ init _ inc body -> stmtsAreNonMonadic init &&
>				            stmtsAreNonMonadic inc  &&
>				            stmtsAreNonMonadic body
>                ISWhile _ _ body ->        stmtsAreNonMonadic body
>                ISBeginEnd _ body ->       stmtsAreNonMonadic body
>                ISIf _ _ con Nothing ->    stmtsAreNonMonadic con
>                ISIf _ _ con (Just alt) -> stmtsAreNonMonadic con &&
>				            stmtsAreNonMonadic alt
>                ISCase _ _ cs d         -> (all caseIsNonMonadic cs) &&
>				            defaultIsNonMonadic d
>                ISCaseTagged _ _ cs d   -> (all caseTIsNonMonadic cs) &&
>				            defaultIsNonMonadic d
>	         _ -> False
>	     where caseIsNonMonadic  (_, _, ss)       = stmtsAreNonMonadic ss
>	           caseTIsNonMonadic (_, _, _, ss)    = stmtsAreNonMonadic ss
>	           defaultIsNonMonadic Nothing        = True
>	           defaultIsNonMonadic (Just (_, ss)) = stmtsAreNonMonadic ss


 >     let fn = (case stmt of
 >                ISDecl _ _ _ _ ->
 >                ISPatEq _ _ _ ->
 >                ISPatBind _ _ _ ->
 >                ISEqual _ _ _ ->
 >                ISUpdate _ _ _ ->
 >                ISUpdateBind _ _ _ ->
 >                ISUpdateReg  _ _ _ ->
 >                ISRegWrite _ _ _ ->
 >                ISBind _ _ _ _ ->
 >                ISReturn _ _ ->
 >                ISNakedExpr _ _ ->
 >                ISInst _ _ _ _ _ _ _ _ _ ->
 >                ISFunction _ _ _ ->
 >                ISRule _ _ _ _ ->
 >                ISMethod _ _ ->
 >                ISFor _ _ _ _ _ ->
 >                ISWhile _ _ _ ->
 >                ISBeginEnd _ _ ->
 >                ISAction _ _ ->
 >                ISActionValue _ _ ->
 >                ISIf _ _ _ _ ->
 >                ISCase _ _ _ _ ->
 >                ISCaseTagged _ _ _ _ ->
 >                ISSeq _ _ ->
 >                ISPar _ _ ->
 >                ISSequence _ _ ->
 >                ISProperty _ _ ->
 >                ISAssertStmt _ _ ->
 >                ISTypedef _ _ ->
 >                ISModule _ _ _ _ _ ->
 >                ISForeignModule _ _ _ _ ->
 >                ISInterface _ _ _ _ _ ->
 >                ISTypeclass _ _ _ _ _ _ ->
 >                ISTypeclassInstance _ _ _ ->
 >                ISImport _ _ ->
 >                ISExport _ _ ->
 >                ISBVI _ _ ->
 >                ISClassicDefns _ _ ->
