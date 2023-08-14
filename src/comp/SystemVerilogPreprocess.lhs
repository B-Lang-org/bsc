> {-# OPTIONS_GHC -Wall -fno-warn-unused-matches -fno-warn-name-shadowing #-}

Preprocessor for SystemVerilog

> module SystemVerilogPreprocess(preprocess) where

> import Data.List
> import Data.Char(isLetter, isDigit)
> import Control.Monad (when)

> import Position
> import Error(internalError, ErrMsg(..), ErrorHandle, bsError, bsErrorUnsafe)
> import FileIOUtil(readFilePathOrAbs)
> import Version(versionname)
> import Flags(Flags, backend, defines, verbose, ifcPath, cpp, vpp)
> import Backend
> import Util(isWhitespace, fromMaybeM)
> import CPPLineDirectives

> data EnvVal = EnvVal{
>                      env_def      :: String,
>                      env_operands :: [String],
>                      env_value    :: String,
>                      env_pos      :: Position
>                     }
>             | EnvInclude {
>                           env_inc :: String
>                          } deriving( Show )

The state contains
 * reverse list of strings for output
 * current position
 * remaining input characters
 * environment (defs and included files)
 * error handle
 * flags

> newtype PreState = PreState ([String], Position, String, [EnvVal], ErrorHandle, Flags)

> type PreProcessor = PreState -> IO (String, [EnvVal])

> emptyEnv :: [EnvVal]
> emptyEnv = [EnvVal{ env_def = "bluespec",
>                      env_operands = [],
>                      env_value = versionname,
>                      env_pos =initialPosition "Prelude"},
>             EnvVal{ env_def ="BLUESPEC",
>                      env_operands = [],
>                      env_value = versionname,
>                      env_pos = initialPosition "Prelude"}]

> emptyOutput :: [String]
> emptyOutput = []

Scan is not in a monad because of laziness requirements (space efficiency)

> preprocess :: ErrorHandle
>            -> Flags
>            -> Position  -- initial position
>            -> String    -- input
>            -> IO (String,[String])
> preprocess errh flags initPos file0 = do
>     -- perform cpp if requested
>     let file1 = if (cpp flags)
>                 then unlines (map cppLine_to_svLine (lines file0))
>                 else file0
>     -- perform vpp if requested
>     let flagsEnv = populateEnvFromFlags flags
>         state0 = PreState (emptyOutput, initPos, file1,
>                            flagsEnv ++ emptyEnv, errh, flags)
>     (file2, eis) <- if (vpp flags)
>                     then prescanMain state0
>                     else return (file1, [])
>     let include_files = map env_inc [ei | ei@(EnvInclude {} ) <- eis ]
>     -- return the (possibly processed) contents
>     -- and a list of the included files (for dependency checking)
>     return (file2, include_files)

> populateEnvFromFlags :: Flags ->  [EnvVal]
> populateEnvFromFlags  flags = map processFlagString (splitStrings ++ extras)
>     where
>     extras = case (backend flags) of
>                Just Bluesim -> [("__GENC__","")]
>                Just Verilog -> [("__GENVERILOG__","")]
>                Nothing -> []
>     position = newPosition "CommandLine" (-2) (-1)
>     splitStrings = map (break (== '=')) (defines flags)
>     processFlagString :: (String,String) -> EnvVal
>     processFlagString (def1,[])   = EnvVal{ env_def = def1, env_operands = [], env_value = "", env_pos = position}
>     processFlagString (def1,def2) = EnvVal{ env_def = def1, env_operands = [], env_value = (tail def2), env_pos = position}
>

> emitPos :: Position -> Int -> String
> emitPos p val = " `line(" ++ (getPositionFile p) ++ ","
>                         ++ show (getPositionLine p) ++ ","
>                         ++ show (getPositionColumn p) ++ ","
>                         ++ show (val) ++ ")"

> emitLine :: Position -> Int -> String
> emitLine p val = " `line " ++ show (getPositionLine p) ++ " "
>                         ++ show (getPositionFile p) ++ " "
>                         ++ show (val) ++ "\n"

> inEnv :: String -> [EnvVal] -> Bool
> inEnv s e = let e' = [e | e@(EnvVal {} ) <- e]
>             in any (\x -> (env_def x) == s) e'

> getEnvEntry :: String -> [EnvVal] -> EnvVal
> getEnvEntry str [] = internalError ("getEnvEntry: " ++ str ++ " is not defined")
> getEnvEntry str (EnvInclude {}: rest)  = getEnvEntry str rest
> getEnvEntry str (cur@(EnvVal {}):rest) = if (str==(env_def cur)) then cur else (getEnvEntry str rest)


To avoid using stack space, we add each output string to the state,
to the head of a list, that we will reverse and concat at the end

> enstring :: String -> PreState -> PreState
> enstring str (PreState (outp, pos, inp, env, errh, flgs)) =
>    PreState (str:outp, pos, inp, env, errh, flgs)

Toplevel scanner function

> prescanMain :: PreProcessor
> -- end of file
> --   note that we don't know its position, so we can't accurately reproduce
> --   spaces at the end of the file
> prescanMain state@(PreState (outp, pos, [], env, errh, flgs)) =
>     return (concat (reverse outp), env)
> -- Comments are handled correctly so people can comment out "bad"defines
> -- line comment
> prescanMain state@(PreState (outp, pos, '/':'/':input, env, errh, flgs)) =
>     prescanLineComment pos (enstring "//" (eatChars 2 state))
> -- block comment
> prescanMain state@(PreState (outp, pos, '/':'*':input, env, errh, flgs)) =
>     prescanBlockComment (enstring "/*" (eatChars 2 state))

`"  (double quote ")

> prescanMain state@(PreState (outp, pos, ( '`':'\"':restOfInput), env, errh, flgs))
>     = (prescanMain (eatChars 1 state))

-- `\

> prescanMain state@(PreState (outp, pos, ( '`':'\\':restOfInput), env, errh, flgs))
>     = (prescanMain (eatChars 1 state))

> -- `line compiler directive we can ignore it (i.e. pass it on)
> prescanMain state@(PreState (outp, pos, ( '`':'l':'i':'n':'e':c:restOfInput ), env, errh, flgs))
>     | (c=='(' || isWhitespace c) = prescanMain (enstring ('`':'l':'i':'n':'e':c:[]) (eatChars 6 state))
> -- `endif. If we see this something is wrong
> prescanMain state@(PreState (outp, pos, ( '`':'e':'n':'d':'i':'f':c:restOfInput ), env, errh, flgs))
>     | isWhitespace c = bsError errh [(pos, ESVPUnmatchedEndIf)]


> prescanMain state@(PreState (outp, pos, ('`':'i':'f':'d':'e':'f':c:restOfInput),
>                                env, errh, flgs))
>     | isWhitespace c = prescanIfDefDirective True pos (eatChars 7 state)
> prescanMain state@(PreState (outp, pos, ('`':'i':'f':'n':'d':'e':'f':c:restOfInput),
>                                env, errh, flgs))
>     | isWhitespace c = prescanIfDefDirective False pos (eatChars 8 state)
> prescanMain state@(PreState (outp, pos, ('`':'i':'n':'c':'l':'u':'d':'e':
>                                          c:restOfInput ), env, errh, flgs))
>     | isWhitespace c =
>         let
>             (ws, restOfInput2) = span (isWhitespace) restOfInput
>             restOfInput3 = case restOfInput2 of
>                       ('`':rest) -> fst (prescanReplace errh rest pos env)
>                       -- EOF (empty list) will be handled below
>                       _ -> restOfInput2
>             (ws2, restOfInput4) = span (isWhitespace) restOfInput3
>             (delim1, delim2, restOfInput5) =
>                 case restOfInput4 of
>                     ('\"':rest) -> ('\"', '\"', rest)
>                     ('<':rest)  -> ('<',  '>',  rest)
>                     -- The following also handles EOF (empty list)
>                     _    -> let pos' = updatePosString pos
>                                            ("`include" ++ (c:ws))
>                             in  bsErrorUnsafe errh [(pos', ESVPNoImportDelimiter)]
>             (filestr, restOfInput6) = span (/= delim2) restOfInput5
>             furtherInput =
>               case restOfInput6 of
>                 (h:rest) | (h == delim2) -> rest
>                 -- The following also handles EOF (empty list)
>                 _ -> -- XXX ESVPNoImportDelimiter isn't quite right
>                      let pos' = updatePosString pos
>                                     ("`include" ++ (c:ws) ++ (delim1:filestr))
>                      in  bsErrorUnsafe errh [(pos', ESVPNoImportDelimiter)]
>             newPos = updatePosString pos ("`include" ++ (c:ws) ++ ws2 ++
>                                           (delim1:filestr) ++ [delim2])
>             missingFileErr =
>                  bsError errh [(pos, EMissingIncludeFile filestr)]
>         in
>           do
>               (fileContents, fileName) <-
>                   fromMaybeM missingFileErr $
>                       readFilePathOrAbs errh pos (verbose flgs) filestr (ifcPath flgs)
>               let env' = (EnvInclude fileName):env
>               (str,newEnv) <- prescanMain (PreState(emptyOutput, initialPosition fileName,
>                                                     fileContents, env', errh, flgs))
>               prescanMain (enstring ((emitLine (initialPosition fileName) 1) ++ str ++
>                                      (emitLine newPos 2))
>                                     (PreState (outp, newPos, furtherInput, newEnv, errh, flgs)))
>
> prescanMain state@(PreState (outp, pos, ('`':'r':'e':'s':'e':'t':'a':'l':'l':
>                                          c:restOfInput), env, errh, flgs))
>     | isWhitespace c = let
>                           (PreState (_,p,i,_,_,f)) = (eatChars 10 state)
>                           includes = [ei | ei@(EnvInclude {}) <- env]
>                         in
>                           prescanMain(PreState (outp, p, i, emptyEnv ++ includes, errh, f))
> prescanMain state@(PreState (outp, pos, ('`':'u':'n':'d':'e':'f':
>                                          c:restOfInput), env, errh, flgs))
>     | isWhitespace c = let
>                           (ws, idandRest)   = span (isWhitespace) restOfInput
>                           (tid, andRest) = span (isIdChar)  idandRest
>                           newPos = updatePosString pos ("`undef" ++ c:[] ++
>                                                         ws ++ tid)
>                           --toss definitions of id (possibly >1)
>                           newEnv = filter (\x -> ((env_def x) /= tid)) [e' | e'@(EnvVal {}) <- env]
>                        in
>                         do
>                          when (tid == "") $ bsError errh [(pos, ESVPNoId "`undef")]
>                          prescanMain (PreState (outp, newPos, (andRest), newEnv, errh, flgs))
>
> prescanMain state@(PreState (outp, pos, ('`':'d':'e':'f':'i':'n':'e':
>                                          c:restOfInput ), env, errh, flgs))
>     | isWhitespace c =
>         let
>            keywords =
>             ["celldefine","default_nettype","define","else",
>              "elsif","endcelldefine","endif","ifdef","ifndef",
>              "include","line","nounconnected_drive","resetall",
>              "timescale","unconnected_drive","undef", "bluespec",
>              "BLUESPEC"]
>            acquireblock :: String -> (String,String)
>            acquireblock ('/':'/':input) =
>              let
>                (line, rest) = span (/= '\n') input
>              in
>                if ((not (null line)) && (last line) == '\\') then
>                  -- non-terminating line comment
>                  case rest of
>                    (cr:rest') -> let (l,r) = acquireblock rest
>                                  in  ('/':'/':line ++(cr:l),r)
>                    -- EOF
>                    -- XXX Should this be an error?
>                    [] -> ('/':'/':line, [])
>                else
>                  ([],'/':'/':input) -- line comment which ends it
>            acquireblock ('/':'*':input) =
>                 let -- treat like a single line
>                    finishMultiline [] = ([],[])
>                    finishMultiline ('*':'/':input)=
>                       let
>                         (l,r) = acquireblock input
>                       in
>                         ('*':'/':l,r)
>                    finishMultiline (c:input) =
>                       let
>                         (l,r) = finishMultiline input
>                       in
>                         (c:l,r)
>                    (l,r) = finishMultiline input
>                 in
>                   ('/':'*':l,r)
>            -- ignore \r which are found in files written under dos ^J^M newlines
>            acquireblock ( '\\':'\r':input) = acquireblock( '\\':input )
>            acquireblock ('\\':'\n':input) =
>                   let
>                      (l,r) = acquireblock input
>                   in
>                     ('\n':l,r)
>            acquireblock ('\n':input) = ("\n",input)
>            acquireblock (c:input)  = let
>                                         (l,r) = acquireblock input
>                                      in
>                                        (c:l,r)
>            acquireblock [] = ([],[])
>
>            (ws, idandRest)   = span (isWhitespace) restOfInput
>            (uid, andRest) = span (\x -> (isIdChar x) && x /= '(')  idandRest
>            id = if (uid == "") then
>                   bsErrorUnsafe errh [(pos, ESVPInvalidDefId "")]
>                  else
>                   if (elem uid keywords) then
>                      bsErrorUnsafe errh [(pos, ESVPInvalidDefIdKeyword uid)]
>                    else
>                      if (isIdStart (head uid)) then
>                         uid
>                       else
>                         bsErrorUnsafe errh [(pos, ESVPInvalidDefId uid)]
>            (ws2, rest)   = span (isHorizontalWhitespace) andRest
>            (paramlist, postlist, paramtext)=
>               case rest of
>                 ('(':t) -> -- Sadness there are parameters
>                    let
>                       (params, block) = (span ( /=')' ) t)
>                       list = Data.List.groupBy (\x -> \y -> (x /= ',') &&
>                                                             (y /= ',')) params
>                       exclude '\\' = True
>                       exclude c   = isWhitespace c
>                       param_list = map (filter (not . exclude))
>                                         (filter ( /= ",") list)
>                    in
>                      (param_list, (tail block), '(':(params ++ ")") )
>                 _ -> ([],rest, [])--no parameters
>            (defineblock, otherstuff) = acquireblock postlist
>            blockPos = updatePosString pos ("`define"++[c]++ws++
>                                             id++ws2++paramtext)
>            entry = if (nub paramlist /= paramlist) then
>                       bsErrorUnsafe errh [(pos, ESVPRepeatedParamLabel id)]
>                     else
>                       EnvVal{ env_def = id, env_operands = paramlist,
>                               env_value = defineblock, env_pos = blockPos}
>            newPos = (updatePosString pos
>                      (ws ++ id ++ ws2 ++ paramtext ++ defineblock))
>          in
>            prescanMain (enstring (emitPos newPos 0)
>                             (PreState (outp,
>                                        updatePosString pos
>                                        ("`define" ++ c:[] ++ ws ++ id ++
>                                         ws2 ++ paramtext ++ defineblock),
>                                       otherstuff,
>                                       entry:env,
>                                       errh,
>                                       flgs)))
> -- This would be expanding out instances of defines
> prescanMain state@(PreState (outp, pos, '`':restOfInput, env, errh, flgs)) =
>     let
>        (id, paramsAndStuff) = span (isIdChar) restOfInput
>     in do
>         when (id == "") $ bsError errh [(pos, ESVPNoId "`")]
>         case paramsAndStuff of
>             ('(':parms_etc) ->
>              let
>                (params, block) = (get_params parms_etc)
>                get_after [] = bsErrorUnsafe errh [(pos, ESVPNoClosingParen "parameters of `define")]
>                get_after x = tail x
>                afterDefine = get_after block
>                param_list  = ppsplit_params params
>                envEntry = if not (inEnv id env) then
>                             bsErrorUnsafe errh [(pos, ESVPUndefinedId id)]
>                           else
>                             (getEnvEntry id env)
>                (pnames,torep,bpos) = (env_operands envEntry, env_value envEntry, env_pos envEntry )
>                replist = let
>                             whatType x = if (isWhitespace x) then (0::Int)
>                                           else
>                                             if (isIdChar x) then (1::Int)
>                                              else
>                                                (2::Int)
>                          in
>                           Data.List.groupBy (\x -> \y ->
>                                              ((whatType x)==(whatType y))) torep
>                replaceParams :: [String] -> [String]
>                              -> [String] -> [String]
>                --so that we don't double replace parameters
>                --(e.g. if we have params "foo" -> "bar" and "bar" -> "baz"
>                --      we expect "foo" to become "bar" not "baz"
>
>                replaceParams p r [] = []
>                replaceParams p r (h:t) =
>                     case (elemIndex h p) of
>                          Nothing -> h : (replaceParams p r t)
>                          (Just n)-> ((r !! n)) : (replaceParams p r t)
>                fin_list = if ((length pnames) /= (length param_list)) then
>                              bsErrorUnsafe errh
>                                            [(pos, ESVPWrongNumParams id
>                                                     (length pnames)
>                                                     (length param_list))]
>                            else
>                              (replaceParams pnames param_list replist)
>                -- stitch things together.
>                str_before_merge = (foldr (++) "" fin_list)
>                mergeStr [] = []
>                mergeStr (c:'`':'`':rest) | isWhitespace c = mergeStr ('`':'`':rest)
>                mergeStr ('`':'`':c:rest) | isWhitespace c = mergeStr ('`':'`':rest)
>                mergeStr ('`':'`':'`':'l':'i':'n':'e':rest) = mergeStr1 rest
>                mergeStr ('`':'`':rest) = mergeStr rest
>                mergeStr (c:rest) = c:(mergeStr rest)
>                mergeStr1 [] = []
>                mergeStr1 (')':rest) = mergeStr rest
>                mergeStr1   (c:rest) = mergeStr1 rest
>                finalblockToParse = mergeStr str_before_merge
>                nPos  = (updatePosString pos (('`':id)++"("++params++")"))
>                nPos' = (updatePosString pos (('`':id)++"("))
>                total_reduced nstr = ('`':id)++"("++nstr++")"
>              in
>                do
>                  (reduced,_) <-
>                           prescanMain (PreState (emptyOutput, nPos', params, env, errh, flgs))
>                  -- if the argument has preprocessor directives, we do something different
>                  -- XXX why? what?
>                  rslt <- if (reduced == params)
>                    then do (defstr,newEnv) <-
>                               prescanMain (PreState (emptyOutput, bpos, finalblockToParse, env, errh, flgs))
>                            prescanMain (enstring ((emitPos bpos 1) ++ defstr ++ (emitPos nPos 2))
>                                             (PreState (outp, nPos, afterDefine, newEnv, errh, flgs)))
>                    else do (defstr,newEnv) <-
>                               prescanMain (PreState (emptyOutput, pos, (total_reduced reduced), env, errh, flgs))
>                            prescanMain (enstring ((emitPos bpos 1) ++ defstr ++ (emitPos nPos 2))
>                                             (PreState (outp, nPos, afterDefine, newEnv, errh, flgs)))
>                  return rslt
>             _ -> if not (inEnv id env) then
>                     bsError errh [(pos, ESVPUndefinedId id)]
>                   else
>                     let
>                        envEntry = getEnvEntry id env
>                        (list,str, bpos) = (env_operands envEntry, env_value envEntry, env_pos envEntry)
>                        nPos = if (list /= []) then
>                                  bsErrorUnsafe errh
>                                                [(pos, ESVPWrongNumParams id
>                                                         (length list) 0)]
>                                else
>                                  (updatePosString pos ('`':id))
>                      in
>                        do
>                          (defstr,newEnv) <-
>                             prescanMain (PreState (emptyOutput, bpos, str, env, errh, flgs))
>                          prescanMain (enstring ((emitPos bpos 1) ++ defstr ++ (emitPos (nPos) 2))
>                                           (PreState (outp, nPos, paramsAndStuff, env, errh, flgs)))
>
> -- other stuff
> prescanMain state@(PreState (outp, pos, c:restOfInput, env, errh, flgs)) =
>     prescanMain (enstring (c:[]) (eatChars 1 state))

Handle replacements

> prescanReplace :: ErrorHandle -> String -> Position -> [EnvVal] -> (String,Position)
> prescanReplace errh str pos env =
>     let
>        (id, paramsAndStuff) = span (isIdChar) str
>     in
>        if (id == "") then bsErrorUnsafe errh [(pos, ESVPNoId "`")]
>        else
>         case paramsAndStuff of
>             ('(':parms_etc) ->
>              let
>                (params, block) = (get_params parms_etc)
>                get_after [] = bsErrorUnsafe errh [(pos, ESVPNoClosingParen "parameters of `define")]
>                get_after x = tail x
>                afterDefine = get_after block
>                param_list  = ppsplit_params params
>                envEntry = if not (inEnv id env) then
>                                           bsErrorUnsafe errh [(pos, ESVPUndefinedId id)]
>                                         else
>                                           getEnvEntry id env
>                (pnames,torep) = (env_operands envEntry, env_value envEntry)
>                replist = let
>                             whatType x = if (isWhitespace x) then (0::Int)
>                                           else
>                                             if (isIdChar x) then (1::Int)
>                                              else
>                                                (2::Int)
>                          in
>                           Data.List.groupBy (\x -> \y ->
>                                              ((whatType x)==(whatType y))) torep
>                replaceParams :: [String] -> [String]
>                              -> [String] -> [String]
>                --so that we don't double replace parameters
>                --(e.g. if we have params "foo" -> "bar" and "bar" -> "baz"
>                --      we expect "foo" to become "bar" not "baz"
>
>                replaceParams p r [] = []
>                replaceParams p r (h:t) =
>                     case (elemIndex h p) of
>                          Nothing -> h : (replaceParams p r t)
>                          (Just n)-> ((r !! n)) : (replaceParams p r t)
>                fin_list = if ((length pnames) /= (length param_list)) then
>                              bsErrorUnsafe errh [(pos, ESVPWrongNumParams id
>                                                          (length pnames)
>                                                          (length param_list))]
>                            else
>                              (replaceParams pnames param_list replist)
>                -- stitch things together.
>                str_before_merge = (foldr (++) "" fin_list)
>                mergeStr [] = []
>                mergeStr (c:'`':'`':rest) | isWhitespace c = mergeStr ('`':'`':rest)
>                mergeStr ('`':'`':c:rest) | isWhitespace c = mergeStr ('`':'`':rest)
>                mergeStr ('`':'`':'`':'l':'i':'n':'e':rest) = mergeStr1 rest
>                mergeStr ('`':'`':rest) = mergeStr rest
>                mergeStr (c:rest) = c:(mergeStr rest)
>                mergeStr1 [] = []
>                mergeStr1 (')':rest) = mergeStr rest
>                mergeStr1   (c:rest) = mergeStr1 rest
>                finalblockToParse = mergeStr str_before_merge
>                nPos  = (updatePosString pos (('`':id)++"("++params++")"))
>                nPos' = (updatePosString pos (('`':id)++"("))
>                total_reduced nstr = ('`':id)++"("++nstr++")"
>                (reduced,_) = prescanReplace errh params nPos' env
>              in
>                if (reduced == params)
>                   then (finalblockToParse ++ afterDefine, nPos)
>                   else let
>                          (str', _) = prescanReplace errh (total_reduced reduced) pos env
>                        in
>                          (str' ++ afterDefine, nPos)
>             _ -> if not (inEnv id env) then
>                     bsErrorUnsafe errh [(pos, ESVPUndefinedId id)]
>                   else
>                     let
>                        cEntry = (getEnvEntry id env)
>                        list = env_operands cEntry
>                        nPos = if (list /= []) then
>                                  bsErrorUnsafe errh
>                                                [(pos, ESVPWrongNumParams id
>                                                         (length list) 0)]
>                                else
>                                  (updatePosString pos ('`':id))
>                      in
>                        ((env_value cEntry) ++ paramsAndStuff,nPos)

Split a string into two strings, the parameters and the "rest" while:
  - ignoring `line expressions
  - tracking open and close parens so the correct closing paren is
    used to mark the end of the parameters

> get_params :: String -> (String, String)
> get_params str = getprms False 0 str
>    where getprms :: Bool -> Int -> String -> (String, String)
>          getprms False cnt ('`':'l':'i':'n':'e':c:rest) | (isWhitespace c) =
>             getprms False cnt ('`':'l':'i':'n':'e':rest)
>          getprms False cnt ('`':'l':'i':'n':'e':'(':rest) =
>             let (a,b) = getprms True cnt rest
>             in  (('`':'l':'i':'n':'e':'(':a),b)
>          getprms False cnt [] = ([],[])
>          getprms False cnt ('(':rest) =
>             cons_fst '(' (getprms False (cnt + 1) rest)
>          getprms False 0   (')':rest) = ([],(')':rest))
>          getprms False cnt (')':rest) =
>             cons_fst ')' (getprms False (cnt - 1) rest)
>          getprms False cnt (c:rest) =
>             cons_fst c (getprms False cnt rest)
>          getprms True cnt [] =  internalError ("get_params: `line is missing closing paren")
>          getprms True cnt (')':rest) =
>             cons_fst ')' (getprms False cnt rest)
>          getprms True cnt (c:rest)   =
>             cons_fst c (getprms True cnt rest)
>
>          cons_fst c (a,b) = ((c:a),b)

Split a comma separated string into a list of parameters while:
  - ignoring `line expressions
  - tracking open and close parens so nested commas etc.
    don't confuse parameter splitting

> ppsplit_params :: String -> [String]
> ppsplit_params str = ppsplit' False 0 str
>    where ppsplit' :: Bool -> Int -> String -> [String]
>          ppsplit' False cnt ('`':'l':'i':'n':'e':c:rest) | (isWhitespace c) =
>             ppsplit' False cnt ('`':'l':'i':'n':'e':rest)
>          ppsplit' False cnt ('`':'l':'i':'n':'e':'(':rest) =
>             case ppsplit' True cnt rest of
>               (a:b) -> (('`':'l':'i':'n':'e':'(':a):b)
>               _ -> internalError ("ppsplit_params: `line is missing closing paren")
>          ppsplit' False cnt [] = []
>          ppsplit' False cnt ('(':rest) =
>             cons_fst '(' (ppsplit' False (cnt + 1) rest)
>          ppsplit' False cnt (')':rest) =
>             cons_fst ')' (ppsplit' False (cnt - 1) rest)
>          ppsplit' False 0 (c:rest) | c == ',' =
>             ([]:ppsplit' False 0 rest)
>          ppsplit' False cnt (c:rest) =
>             cons_fst c (ppsplit' False cnt rest)
>          ppsplit' True cnt [] =  internalError ("ppsplit_params: `line is missing closing paren")
>          ppsplit' True cnt (')':rest) =
>             cons_fst ')' (ppsplit' False cnt rest)
>          ppsplit' True cnt (c:rest)   =
>             cons_fst c   (ppsplit' True  cnt rest)
>
>          cons_fst c []    = [[c]]
>          cons_fst c (a:b) = ((c:a):b)

Line comments

> prescanLineComment :: Position     -- init position
>                    -> PreProcessor -- the scanner, i.e., state -> tokens
> prescanLineComment initPos (PreState (outp, pos, input, env, errh, flgs)) =
>     let (commentText, afterCommentText) = span (/= '\n') input
>         newPos = updatePosString pos commentText
>     in
>         prescanMain
>             (enstring commentText
>                  (PreState(outp, newPos, afterCommentText, env, errh, flgs)))

Block Comments

> prescanBlockComment :: PreProcessor
> -- the scanner, i.e., state -> tokens
> prescanBlockComment (PreState (outp, pos, '*':'/':input, env, errh, flgs)) =
>     let nextScannerState = PreState (outp, updatePosString pos "*/", input, env, errh, flgs)
>     in  prescanMain (enstring "*/" nextScannerState)
> prescanBlockComment (PreState (outp, pos, char:rest, env, errh, flgs)) =
>     prescanBlockComment
>         (enstring (char:[])
>              (PreState (outp, updatePosChar pos char, rest, env, errh, flgs)))
> prescanBlockComment (PreState (outp, pos, [], env, errh, flgs)) =
>     -- no terminate. Scanner will complain
>     prescanMain (PreState (outp, pos, [], env, errh, flgs))

Bool is whether it's a positive if. Position is initial pos of if

> prescanIfDefDirective :: Bool -> Position -> PreProcessor
> prescanIfDefDirective posif initPos state@(PreState (outp, pos, input, env, errh, flgs)) =
>  --read whitespace head and get id
>  let
>     getallIf :: String -> Int -> (String,String)
>     getallIf  ('`':'i':'f':'d':'e':'f':c:rest ) n
>               | isWhitespace c = ( '`':'i':'f':'d':'e':'f':c:fst,snd)
>                 where (fst,snd) = (getallIf rest (n+1))
>     getallIf  ( '`':'i':'f':'n':'d':'e':'f':c:rest ) n
>              | isWhitespace c =
>                ( '`':'i':'f':'n':'d':'e':'f':c:fst,snd)
>                where (fst,snd) = (getallIf rest (n+1))

This will fail if the file ends with endif with no terminating whitespace
like a newline

>     getallIf  ( '`':'e':'n':'d':'i':'f':c:rest) n
>              | isWhitespace c =
>                if (n == 0) then
>                   ('`':'e':'n':'d':'i':'f':[],c:rest)
>                 else
>                   let
>                     (fst,snd) = (getallIf rest (n-1))
>                   in
>                     ( '`':'e':'n':'d':'i':'f':c:fst,snd)
>     getallIf  (c:rest) n  = (c:fst,snd)
>                where (fst,snd) = (getallIf rest n)
>     getallIf [] n = -- unclosed if
>                ([],[])

>     grab1stBit :: String -> Int -> String
>     grab1stBit [] n = [] -- whole thing is 1 clause
>     grab1stBit ('`':'i':'f':'d':'e':'f':c:rest) n
>              | isWhitespace c = ('`':'i':'f':'d':'e':'f':
>                                  c:(grab1stBit rest (n+1)))
>     grab1stBit ('`':'i':'f':'n':'d':'e':'f':c:rest) n
>              | isWhitespace c = ('`':'i':'f':'n':'d':'e':'f':
>                                  c:(grab1stBit rest (n+1)))
>     grab1stBit ('`':'e':'n':'d':'i':'f':[]) 0 = []
>     grab1stBit ('`':'e':'n':'d':'i':'f':c:rest) 0
>              | isWhitespace c = []
>     grab1stBit ('`':'e':'n':'d':'i':'f':c:rest) n
>              | isWhitespace c = ('`':'e':'n':'d':'i':'f':
>                                  c:(grab1stBit rest (n-1)))
>     grab1stBit ('`':'e':'l':'s':'i':'f':c:rest) 0
>              | isWhitespace c = [] -- end of first clause
>     grab1stBit ('`':'e':'l':'s':'i':'f':c:rest) n
>              | isWhitespace c = ('`':'e':'l':'s':'i':'f':
>                                  c:(grab1stBit rest n))
>     grab1stBit ('`':'e':'l':'s':'e':c:rest) 0
>              | isWhitespace c = [] -- end of first clause
>     grab1stBit ('`':'e':'l':'s':'e':c:rest) n
>              | isWhitespace c = ('`':'e':'l':'s':'e':
>                                  c:(grab1stBit rest n))
>     grab1stBit (c:rest) n = (c:(grab1stBit rest (n)))

toss1stBit returns the `else part to the end of the `endif

It probably won't work properly if and there are unbalanced `ifdef
(etc) statements in an include, or if `ifdefs (etc) are commented

>     toss1stBit :: String -> Int -> String
>     toss1stBit [] n = [] -- whole thing is 1 clause
>     toss1stBit ('`':'i':'f':'d':'e':'f':c:rest) n
>              | isWhitespace c = (toss1stBit rest (n+1))
>     toss1stBit ('`':'i':'f':'n':'d':'e':'f':c:rest) n
>              | isWhitespace c = (toss1stBit rest (n+1))
>     toss1stBit ('`':'e':'n':'d':'i':'f':[]) 0
>              ='`':'e':'n':'d':'i':'f':[]
>     toss1stBit ('`':'e':'n':'d':'i':'f':c:rest) 0
>              | isWhitespace c ='`':'e':'n':'d':'i':'f':c:rest
>     toss1stBit ('`':'e':'n':'d':'i':'f':c:rest) n
>              | isWhitespace c = (toss1stBit rest (n-1))
>     toss1stBit ('`':'e':'l':'s':'i':'f':c:rest) 0  -- end of first clause
>              | isWhitespace c = '`':'e':'l':'s':'i':'f':c:rest
>     toss1stBit ('`':'e':'l':'s':'i':'f':c:rest) n
>              | isWhitespace c = (toss1stBit rest n)
>     toss1stBit ('`':'e':'l':'s':'e':c:rest) 0 -- end of first clause
>              | isWhitespace c = '`':'e':'l':'s':'e':c:rest
>     toss1stBit ('`':'e':'l':'s':'e':c:rest) n
>              | isWhitespace c = (toss1stBit rest n)
>     toss1stBit (c:rest) n = (toss1stBit rest (n))
>
>     (ws, idandRest)   = span (isWhitespace) input
>     (id, restOfInput) = span (isIdChar) idandRest
>     (ifstmt, rest) = (getallIf restOfInput 0)
>     afterIfPos = updatePosString pos (ws ++ id ++ ifstmt)
>  in
>     do
>       when (id == "") $ let ctx = if posif then "`ifdef" else "`ifndef"
>                         in bsError errh [(pos, ESVPNoId ctx)]
>       (ifStr, newEnv) <-
>           if ((inEnv id env) == posif) then
>              --do first branch
>              --mark this with the right position
>              prescanMain
>                  (enstring (emitPos (updatePosString pos (ws ++ id)) 0)
>                       (PreState (emptyOutput, updatePosString pos (ws ++ id),
>                                  (grab1stBit ifstmt 0), env, errh, flgs)))
>            else --not 1st clause
>              case (toss1stBit ifstmt 0) of
>                ('`':'e':'l':'s':'e':rest) -> --we take this clause
>                 let
>                    newPos = (updatePosString pos
>                              (ws ++ id ++ (grab1stBit ifstmt 0) ++ "`else"))

Losing 6 characters of "`endif"

>                    newInput =take ((length rest)-6) rest
>                 in
>                   prescanMain
>                       (enstring (emitPos newPos 0)
>                            (PreState (emptyOutput, newPos, newInput, env, errh, flgs)))
>                ('`':'e':'l':'s':'i':'f':rest) ->
>                 --check if we take this clause
>                 prescanIfDefDirective True initPos
>                    (PreState (emptyOutput,
>                               updatePosString pos
>                                   (ws ++ id ++(grab1stBit ifstmt 0)++"`elsif"),
>                               rest, env, errh, flgs))
>                _ -> return ([],env) -- only 1 clause so finished
>       prescanMain (enstring (ifStr ++ (emitPos afterIfPos 0))
>                        (PreState (outp, afterIfPos, rest, newEnv, errh, flgs)))


SYSTEM VERILOG CHARACTER CLASSES

> isHorizontalWhitespace :: Char -> Bool
> isHorizontalWhitespace ' ' = True
> isHorizontalWhitespace '\t' = True
> isHorizontalWhitespace _ = False

Does a character start a valid identifier?

> isIdStart :: Char -> Bool
> isIdStart '_' = True -- might be faster as a full table
> isIdStart c   = isLetter c

Does a character continue a valid identifier?

> isIdChar :: Char -> Bool
> isIdChar '_' = True -- might be faster as a full table
> isIdChar '$' = True
> isIdChar c   = isLetter c || isDigit c


UTILITY FUNCTIONS

Eat n characters of input, updating the position

> eatChars :: Int -> PreState -> PreState
> eatChars 0 state = state
> eatChars n (PreState (outp, pos, c:input, env, errh, flgs)) =
>     eatChars (n-1) (PreState (outp, updatePosChar pos c, input, env, errh, flgs))
> eatChars n (PreState (outp, pos, "", env, errh, flgs)) =
>     internalError ("eatChars " ++ show n ++ ": no input left")
