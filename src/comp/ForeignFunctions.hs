{-# LANGUAGE CPP #-}
module ForeignFunctions ( ForeignType(..)
                        , ForeignFunction(..)
                        , ForeignCall(..)
                        , Argument(..)
                        , ReturnStyle(..)
                        , ForeignFuncMap
                        , mkForeignFunction
                        , mkImportDeclarations
                        , mkDPIDeclarations
                        , getForeignFunctions
                        , mkFFDecl
                        , encodeArgs
                        , argExpr
                        , mkCallExpr
                        , mkCallAction
                        , isAbsent
                        , isNarrow
                        , isWide
                        , isPoly
                        , isString
                        , wideReturn
                        , polyReturn
                        , toAVId
                        , fromAVId
                        , isAVId
                        , isMappedAVId
                        , toDisplayId
                        , fromDisplayId
                        , isDisplayId
                        , toFileId
                        , fromFileId
                        , isFileId
                        )
  where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import Id(Id, isSignedId, getIdString, qualEq)
import CType
import ASyntax
import ASyntaxUtil
import CCSyntax
import Verilog(VDPI(..), VDPIType(..), mkVId, idToVId)
import ErrorUtil(internalError)
import Util(tailOrErr, itos)
import PPrint hiding (char, int)
import Eval

import Data.List(intercalate, isPrefixOf, nub)
import Data.Maybe(mapMaybe, maybeToList)
import PreIds
import ListMap as LM

import qualified Data.Map as M

-- import Debug.Trace
-- import Util(traces)

-- Represent the width information needed for foreign types
data ForeignType = Void
                 | Narrow Integer
                 | Wide Integer
                 | Polymorphic
                 | StringPtr
  deriving (Eq,Show);

instance PPrint ForeignType where
  pPrint _ _ Void        = text "void"
  pPrint _ _ (Narrow n)  = (text "Bits#(") <> (text (itos n)) <> (text ")")
  pPrint _ _ (Wide n)    = (text "Bits#(") <> (text (itos n)) <> (text ")")
  pPrint _ _ Polymorphic = text "Bits#(?)"
  pPrint _ _ StringPtr   = text "String"

instance NFData ForeignType where
  rnf Void = ()
  rnf (Narrow n) = rnf n
  rnf (Wide n) = rnf n
  rnf Polymorphic = ()
  rnf StringPtr = ()

isAbsent :: ForeignType -> Bool
isAbsent Void = True
isAbsent _    = False

isNarrow :: ForeignType -> Bool
isNarrow (Narrow n) = True
isNarrow _          = False

isWide :: ForeignType -> Bool
isWide (Wide _) = True
isWide _         = False

isPoly :: ForeignType -> Bool
isPoly Polymorphic = True
isPoly _           = False

isString :: ForeignType -> Bool
isString StringPtr = True
isString _         = False

-- Associate a name, return type and argument types to describe
-- a foreign function.
data ForeignFunction = FF { ff_name :: Id
                          , ff_ret  :: ForeignType
                          , ff_args :: [ForeignType]
                          }
  deriving (Eq,Show);

instance PPrint ForeignFunction where
  pPrint d p (FF nm rt args) =
    let name = text (getIdString nm)
        ret_type = pPrint d p rt
        arg_types = pparen True (sepList (map (pPrint d p) args) comma)
    in ret_type <+> name <> arg_types

instance NFData ForeignFunction where
  rnf (FF name ret args) = rnf3 name ret args

mkForeignFunction :: Id -> CType -> ForeignFunction
mkForeignFunction name ty =
  let (args,ret) = getArrows ty
      ret_type = mkFT ret
      arg_types = map mkFT args
  in FF name ret_type arg_types
  where mkFT ty | isTypeString ty  = StringPtr
                | isTypePolyBit ty = Polymorphic
                | (isTypeBit ty) || (isTypeActionValue ty) || (isTypeActionValue_ ty) =
                                     if bitWidth ty > 64
                                     then Wide (bitWidth ty)
                                     else if bitWidth ty == 0
                                          then Void
                                          else Narrow (bitWidth ty)
                | (isTypeAction ty) || (isTypePrimAction ty) = Void
                | otherwise        =
                    internalError $ "mkForeignFunction: unexpected type -- " ++ (show ty)

-- lookup for foreign function info
type ForeignFuncMap = M.Map String ForeignFunction

-- A foreign function can be called as an expression or an action.
-- They can each also call non-foreign functions, but those are
-- not encapsulated as ForeignCalls.
data ForeignCall = FFCall   { fc_func :: ForeignFunction
                            , fc_call :: AExpr
                            }
                 | FFAction { fc_func :: ForeignFunction
                            , fc_action :: AAction
                            }
  deriving (Eq,Show);

fc_args :: ForeignCall -> [AExpr]
fc_args (FFCall _ expr)  = ae_args expr
fc_args (FFAction _ act) = tailOrErr "action has no condition" (aact_args act)

getFn :: ForeignFuncMap -> String -> ForeignFunction
getFn ff_map name =
  case M.lookup name ff_map of
    (Just ff) -> ff
    Nothing   -> internalError $ "unknown foreign function: " ++ name

wideReturn :: ForeignFuncMap -> AExpr -> Bool
wideReturn ff_map expr =
  let ff = getFn ff_map (ae_funname expr)
  in isUserCExpr expr && isWide (ff_ret ff)

polyReturn :: ForeignFuncMap -> AExpr -> Bool
polyReturn ff_map expr =
  let ff = getFn ff_map (ae_funname expr)
  in isUserCExpr expr && isPoly (ff_ret ff)

-- -------------------------------------------------
-- Argument list processing for interfacing to C/C++
-- This handles both foreign and non-foreign calls.

data Argument = Arg     AExpr          -- expression
              | Field   AExpr String   -- expression.field
              | Ptr     AExpr          -- &expression
              | Copy    Argument       -- pointer to copy of value
              | NoConst Argument       -- cast to non-const
              | SimHdl                 -- pointer to the kernel state
              | Module                 -- pointer to enclosing module
              | ArgStr                 -- descr. of arg types and sizes
              | Alloc   Integer Bool   -- newly allocated memory
              | Null                   -- NULL pointer
  deriving (Eq, Show);

data ReturnStyle = None      -- there is no return value
                 | Direct    -- the value is returned from the call
                 | Pointer   -- the value is passed in and overwritten
                 | Buffered  -- storage is allocated and passed in
  deriving (Eq, Show);

instance PPrint ReturnStyle where
    pPrint d p x = text (show x)

instance PPrint Argument where
    pPrint d p (Arg e)     = parens ( text( "Arg" ) <+> pPrint d p e)
    pPrint d p (Field e s) = parens ( text( "Field" ) <+> pPrint d p e <> parens(text s))
    pPrint d p (Ptr e) = parens ( text( "Ptr" ) <+> pPrint d p e )
    pPrint d p (Copy a) = parens ( text( "Copy" ) <+> pPrint d p a)
    pPrint d p (NoConst a) = parens ( text( "NoConst" ) <+> pPrint d p a)
    pPrint d p (SimHdl) = text "SimHdl"
    pPrint d p (Module) = text "Module"
    pPrint d p (ArgStr) = text "ArgStr"
    pPrint d p (Alloc i b) = parens ( text( "Alloc" ) <+> pPrint d p (i,b))
    pPrint d p Null = text "Null"

-- we need to be able to handle unsized strings
is_str_lit :: AExpr -> Bool
is_str_lit (ASStr _ _ _)  = True
is_str_lit _              = False

is_str_def :: AExpr -> Bool
is_str_def (ASDef (ATString _) _) = True
is_str_def _                      = False

is_str_param :: AExpr -> Bool
is_str_param (ASParam (ATString _) _) = True
is_str_param _ = False

is_str :: AExpr -> Bool
is_str e = (is_str_lit e) || (is_str_def e) || (is_str_param e)

is_real :: AExpr -> Bool
is_real e = aType e == ATReal

str_size :: AExpr -> [Char]
str_size (ASDef (ATString Nothing) _) = ""
str_size e                            = show (aSize e)

argExpr :: Argument -> Maybe AExpr
argExpr (Arg e)     = Just e
argExpr (Field e _) = Just e
argExpr (Ptr e)     = Just e
argExpr (Copy a)    = argExpr a
argExpr (NoConst a) = argExpr a
argExpr _           = Nothing

-- we need to be able to distinguish between calls to
-- internal C++ functions and to imported foreign C functions.
isUserCExpr :: AExpr -> Bool
isUserCExpr e@(AFunCall {})   = ae_isC e
isUserCExpr _                 = False

isUserCAction :: AAction -> Bool
isUserCAction a@(AFCall {})      = afcall_isC a
isUserCAction a@(ATaskAction {}) = ataskact_isC a
isUserCAction _                  = False


-- This is used when passing argument type information into our
-- system task implementations.  User foreign C calls should not use it.
encodeArgs :: [Argument] -> String
encodeArgs args =
  let prefix (ASDef _ aid) | isSignedId aid = "-"
      prefix _                              = ""
      encode (Arg e)     | is_str e  = Just ((str_size e) ++ "s")
                         | is_real e = Just "r"
                         | otherwise = Just ((prefix e) ++ (show (aSize e)))
      encode (Field e _) = Just ((prefix e) ++ (show (aSize e)) ++ "p")
      encode (Ptr e)     = if (is_str e)
                           then Just "s"
                           else Just ((prefix e) ++ (show (aSize e)) ++ "p")
      encode (Copy a)    = encode a
      encode (NoConst a) = encode a
      encode _           = Nothing
  in intercalate "," (mapMaybe encode args)

-- A value treated polymorphically must be handled based on the type of
-- the actual expression.
polyArg :: AExpr -> Argument
polyArg e = if aSize e > 64 then Field e "data" else Ptr e
-- Create an Argument value for an AExpr, without copying
noCopy :: (AExpr,ForeignType) -> Argument
noCopy (e,t) | is_str e  = NoConst (Arg e)
             | isWide t  = Field e "data"
             | isPoly t  = polyArg e
             | otherwise = Arg e

-- Create an Argument value for an AExpr, with copying
withCopy :: (AExpr,ForeignType) -> Argument
withCopy (e,t) | is_str e  = NoConst (Copy (Arg e))
               | isWide t  = Copy (Field e "data")
               | isPoly t  = Copy (polyArg e)
               | otherwise = Arg e

-- Create an Argument with allocated storage, as an ignored
-- return value for a foreign call.
ignoreRet :: ForeignCall -> Argument
ignoreRet fc =
  case ff_ret (fc_func fc) of
    (Narrow n)  -> Alloc n False
    (Wide n)    -> Alloc n False
    Polymorphic ->
      case fc of
        (FFAction _ (ATaskAction { ataskact_value_type = ty })) ->
           Alloc (aSize ty) False
        otherwise -> Null
    otherwise   -> Null

-- Create an Argument used as a return buffer.
-- If the expression is already in 32-bit storage, it can
-- be used directly.  If it is not, then it must be copied
-- into 32-bit storage and written back after the call.
forReturn :: (AExpr, ForeignType) -> (ReturnStyle,Argument)
forReturn (e,rt) | aSize e > 64 = (Pointer,  noCopy (e,rt))
                 | isPoly rt    = (Buffered, Alloc (aSize e) True)
                 | aSize e > 32 = (Buffered, Alloc (aSize e) True)
                 | aSize e > 8  = (Direct,   noCopy (e,rt))
                 | otherwise    = (Buffered, Alloc (aSize e) True)

-- Foreign functions which return wide or polymorphic values have
-- a pointer to the storage for the return passed as their first argument.
getReturnArg :: (Maybe (AType,Bool,AId)) -> ForeignType -> (Maybe AExpr)
getReturnArg (Just (ty,isPort,aid)) ft = if isWide ft || isPoly ft
                                         then if isPort
                                              then Just (ASPort ty aid)
                                              else Just (ASDef ty aid)
                                         else Nothing
getReturnArg Nothing         _  = Nothing

-- Convert arguments for a ForeignCall into a list of Arguments suitable
-- for calling the imported function.  This may require copying inputs and
-- adding an argument for the output memory area.  If there is no
-- expression for the return argument to a wide or polymorphic return,
-- space is allocated and passed in.
mkForeignCallArgs :: (Maybe AExpr) -> ForeignCall -> (ReturnStyle,[Argument])
mkForeignCallArgs ret fc =
  let rest = [ withCopy a | a <- zip (fc_args fc) (ff_args (fc_func fc)) ]
      rt = ff_ret (fc_func fc)
  in if isAbsent rt
     then (None,rest)
     else case ret of
            (Just e) -> let (ret_style, e') = forReturn (e,rt)
                        in (ret_style, (e':rest))
            Nothing  -> if isWide rt || isPoly rt
                        then (Buffered,((ignoreRet fc):rest))
                        else (Direct,rest)

-- Generate a (do_writeback, fn name, arg list) tuple for an imported call
-- given an optional return def name and a ForeignCall.
mkForeignCall :: (Maybe (AType,Bool,AId)) -> ForeignCall
                    -> (ReturnStyle,String,[Argument])
mkForeignCall ret fc@(FFCall ff expr) =
  let name = case expr of
               (AFunCall {}) -> ae_funname expr
               otherwise     -> internalError "mkForeignCall: non-call expr"
      ret_expr = getReturnArg ret (ff_ret ff)
      (ret_style,args) = mkForeignCallArgs ret_expr fc
  in (ret_style, name, args)
mkForeignCall ret fc@(FFAction ff action) =
  let name = case action of
               (AFCall {})      -> afcall_fun action
               (ATaskAction {}) -> ataskact_fun action
               otherwise        -> internalError "mkForeignCall: non-foreign action"
      ret_expr = getReturnArg ret (ff_ret ff)
      (ret_style,args) = mkForeignCallArgs ret_expr fc
  in (ret_style, name, args)


-- Determine whether a system task needs a pointer to the kernel state
fnNeedsSimHdl :: String -> Bool
fnNeedsSimHdl name = any (`isPrefixOf` name ) tasks
    where tasks = [ "$time", "$stime"

                  , "$stop", "$finish"

                  , "$test$plusargs"

                  , "$dumpfile" , "$dumpvars"
                  , "$dumpon"   , "$dumpoff"  , "$dumpall"
                  , "$dumplimit", "$dumpflush"

                  -- idPrefixOf handles the "b", "o", "h", "AV" variants
                  , "$write"  , "$fwrite"  , "$swrite"
                  , "$display", "$fdisplay", "$sformat"
                  , "$info"   , "$warning" , "$error", "$fatal"
                  ]

-- Determine whether a system task needs a pointer to its module
fnNeedsLocation :: String -> Bool
fnNeedsLocation name = any (`isPrefixOf` name ) tasks
    where tasks = ["$write"  , "$fwrite"  , "$swrite"
                  ,"$display", "$fdisplay", "$sformat"
                  ,"$info"   , "$warning" , "$error", "$fatal"
                  ]

-- rewrite $<taskname> as dollar_<taskname>
mapFnName :: String -> String
mapFnName s = helper s False
  where helper []       _     = []
        helper ('$':cs) True  = "_dollar_" ++ (helper cs True)
        helper ('$':cs) False = "dollar_" ++ (helper cs True)
        helper (c:cs)   _     = c:(helper cs True)

-- Determine whether a system task needs a pointer to its return value
mkSystemTaskReturn :: AAction -> (ReturnStyle, Maybe Argument)
mkSystemTaskReturn act@(ATaskAction {}) =
  if any (\x -> isPrefixOf x (ataskact_fun act)) tasks
  then case (ataskact_temp act) of
         (Just aid) -> (Pointer, (Just (Ptr (ASDef (ataskact_value_type act) aid))))
         Nothing    -> (Direct, Nothing)
  else (Direct, Nothing)
  where tasks = ["$swrite", "$sformat"]
mkSystemTaskReturn _ = internalError "mkSystemTaskReturn: not a task action"

-- Convert arguments for a ForeignCall into a list of Arguments suitable
-- for calling a system task.  This may require adding a "this" pointer,
-- adding an argument descriptor string, and passing some values by pointer.
mkSystemTaskArgs :: Bool -> Bool -> Maybe Argument -> [AExpr] -> [Argument]
mkSystemTaskArgs add_sim add_this ret_arg args =
  let rest   = map convAExprToArgument args
      sim    = if add_sim then [SimHdl] else []
      this   = if add_this then [Module] else []
      argstr = if (null args) then [] else [ArgStr]
  in sim ++ this ++ argstr ++ (maybeToList ret_arg) ++ rest

convAExprToArgument :: AExpr -> Argument
convAExprToArgument e | (is_str e)     = Ptr e
                      | (is_real e)    = Arg e
                      | (aSize e) > 64 = Ptr e
                      | otherwise      = Arg e


-- Generate a (do_writeback, fn name, arg list) tuple for a system task
-- given a suitable AExpr or AAction
mkSystemTaskCallExpr :: AExpr -> (ReturnStyle,String,[Argument])
mkSystemTaskCallExpr e@(AFunCall {}) =
  let name = ae_funname e
      add_sim = fnNeedsSimHdl name
      add_this = fnNeedsLocation name
      args = mkSystemTaskArgs add_sim add_this Nothing (ae_args e)
  in (Direct, mapFnName name, args)
mkSystemTaskCallExpr e =
  internalError $ "mkSystemTaskCallExpr: non-call expr -- " ++ (show e)


mkSystemTaskCallAction :: AAction -> (ReturnStyle,String,[Argument])
mkSystemTaskCallAction act@(AFCall {}) =
  let name = afcall_fun act
      add_sim = fnNeedsSimHdl name
      add_this = fnNeedsLocation name
      args = mkSystemTaskArgs add_sim add_this
                              Nothing
                              (tailOrErr "action has no condition"
                                         (aact_args act))
  in (None, mapFnName name, args)
mkSystemTaskCallAction act@(ATaskAction {}) =
  let name = ataskact_fun act
      (ret_style,ret_arg) = mkSystemTaskReturn act
      add_sim = fnNeedsSimHdl name
      add_this = fnNeedsLocation name
      args = mkSystemTaskArgs add_sim add_this
                              ret_arg
                              (tailOrErr "action has no condition"
                                         (aact_args act))
  in (ret_style, mapFnName name, args)
mkSystemTaskCallAction act =
  internalError $ "mkSystemTaskCall: non-systask action -- " ++ (show act)

-- versions which handle foreign call detection and lookup

mkCallExpr :: ForeignFuncMap -> Maybe (Bool,AId) -> AExpr ->
              (ReturnStyle,String,[Argument])
mkCallExpr ff_map ret expr =
  let ret' = case ret of
               (Just (isPort,aid)) -> Just (aType expr, isPort, aid)
               Nothing             -> Nothing
      res = if isUserCExpr expr
            then mkForeignCall ret' (FFCall (getFn ff_map (ae_funname expr)) expr)
            else mkSystemTaskCallExpr expr
  in res

mkCallAction :: ForeignFuncMap -> Maybe (Bool,AId) -> AAction ->
                (ReturnStyle,String,[Argument])
mkCallAction ff_map _ action@(AFCall {}) =
  let res = if isUserCAction action
            then mkForeignCall Nothing (FFAction (getFn ff_map (afcall_fun action)) action)
            else mkSystemTaskCallAction action
  in res
mkCallAction ff_map ret action@(ATaskAction {}) =
  let isPort = maybe False fst ret
      ret' = case (ataskact_temp action) of
              (Just aid) -> Just ((ataskact_value_type action), isPort, aid)
              Nothing    -> Nothing
      drop_type (Just (_,p,i)) = Just (p,i)
      drop_type Nothing        = Nothing
  in if (ret /= (drop_type ret'))
     then internalError "mkCallAction: mismatched return values for ATaskAction"
     else if isUserCAction action
          then mkForeignCall ret' (FFAction (getFn ff_map (ataskact_fun action)) action)
          else mkSystemTaskCallAction action
mkCallAction _ _ action =
  internalError $ "mkCallAction: passed method call -- " ++ (show action)

-- =================================================
-- Make a header file with declarations for all foreign functions in
-- the ForeignFuncMap.

toCtype :: ForeignType -> (CCFragment -> CCFragment)
toCtype Void = void
toCtype (Narrow n) | n <= 8    = CCSyntax.char
                   | n <= 32   = unsigned . CCSyntax.int
                   | n <= 64   = unsigned . long . long
                   | otherwise = internalError "Narrow n > 64"
toCtype (Wide _)    = ptr . unsigned . CCSyntax.int
toCtype StringPtr   = ptr . CCSyntax.char
toCtype Polymorphic = ptr . unsigned . CCSyntax.int

mkFFDecl :: ForeignFunction -> CCFragment
mkFFDecl (FF name rt arg_types) =
  let (ret,ats) = if isWide rt || isPoly rt
                  then (Void,(rt:arg_types))
                  else (rt,arg_types)
  in decl $ function (toCtype ret)
                     (mkVar (getIdString name))
                     [ decl $ (toCtype ty) (mkVar "") | ty <- ats ]


mkImportDeclarations :: ForeignFuncMap -> CCFragment
mkImportDeclarations ff_map =
  let ffs = M.elems ff_map
  in program [externC (map mkFFDecl ffs)]

-- =================================================
-- Make the SystemVerilog DPI-C declarations for all foreign functions in
-- the ForeignFuncMap.

mkDPIDeclarations :: [ForeignFunction] -> [VDPI]
mkDPIDeclarations ffuncs = map mkDPIDecl ffuncs
  where
    mkDPIDecl :: ForeignFunction -> VDPI
    mkDPIDecl (FF name rt arg_types) =
      let
          mkResName = mkVId "res"
          mkArgName n = mkVId ("arg" ++ show (n :: Integer))

          mkOut t = (mkResName, False, toVDPIType t)
          mkIn n t = (mkArgName n, True, toVDPIType t)
          mkIns ts = zipWith mkIn [0..] ts

          (vdpi_ret, vdpi_args) =
            if isWide rt || isPoly rt
            then (VDT_void, (mkOut rt : mkIns arg_types))
            else (toVDPIType rt, mkIns arg_types)
      in
         VDPI (idToVId name) vdpi_ret vdpi_args

    toVDPIType :: ForeignType -> VDPIType
    toVDPIType Void = VDT_void
    toVDPIType (Narrow n) | n <= 8    = VDT_byte
                          | n <= 32   = VDT_int
                          | n <= 64   = VDT_longint
                          | otherwise = internalError "Narrow n > 64"
    toVDPIType (Wide n)    = VDT_wide n
    toVDPIType StringPtr   = VDT_string
    toVDPIType Polymorphic = VDT_poly

getForeignFunctions :: ForeignFuncMap -> ASPackage -> [ForeignFunction]
getForeignFunctions ffmap aspkg =
  let
      expr_ff_uses = findAExprs exprForeignCalls aspkg
      expr_ff_names =
        [ i | (AFunCall { ae_funname = i, ae_isC = True }) <- expr_ff_uses ]

      act_ff_uses = concatMap snd (aspkg_foreign_calls aspkg)
      act_ff_names = map afc_fun act_ff_uses

      ff_names = nub (expr_ff_names ++ act_ff_names)

      findFF name = M.lookup name ffmap
  in
      mapMaybe findFF ff_names

-- #############################################################################
-- # Map to and from real Verilog foreign funcs and the BSV AV version.
-- #############################################################################

toAVId :: Id -> Id
toAVId id = case (LM.lookupBy qualEq toAVIdMap id) of
            Just x -> x
            _      -> internalError $ "ForeignFunctions: (toAVId) No AVId exists for " ++ (ppReadable id)


fromAVId :: Id -> Id
fromAVId id = case (LM.lookupBy qualEq fromAVIdMap id) of
              Just x -> x
              _      -> internalError $ "ForeignFunctions: (fromAVId) " ++ (ppReadable id) ++ "is not an AVId"

isAVId :: Id -> Bool
isAVId id = case (LM.lookupBy qualEq fromAVIdMap id) of
            Nothing -> False
            _       -> True

isMappedAVId :: Id -> Bool
isMappedAVId id = case (LM.lookupBy qualEq toAVIdMap id) of
            Nothing -> False
            _       -> True

toAVIdMap :: [(Id, Id)]
toAVIdMap = [ (idSWrite,  idSWriteAV)
            , (idSWriteb, idSWritebAV)
            , (idSWriteo, idSWriteoAV)
            , (idSWriteh, idSWritehAV)
            , (idSFormat, idSFormatAV)
            ]

fromAVIdMap :: [(Id, Id)]
fromAVIdMap =
    let flip (a,b) = (b,a)
    in map flip toAVIdMap

-- #############################################################################
-- # Map to and from $display (and friends) and $write (and friends)
-- #############################################################################

toDisplayId :: Id -> Id
toDisplayId id = case (LM.lookupBy qualEq toDisplayIdMap id) of
            Just x -> x
            _      -> internalError $ "ForeignFunctions: (toDisplayId) No DisplayId exists for " ++ (ppReadable id)


fromDisplayId :: Id -> Id
fromDisplayId id = case (LM.lookupBy qualEq fromDisplayIdMap id) of
              Just x -> x
              _      -> internalError $ "ForeignFunctions: (fromDisplayId) " ++ (ppReadable id) ++ "is not an DisplayId"

isDisplayId :: Id -> Bool
isDisplayId id = case (LM.lookupBy qualEq fromDisplayIdMap id) of
            Nothing -> False
            _       -> True

toDisplayIdMap :: [(Id, Id)]
toDisplayIdMap = [ (idWrite,   idDisplay)
               , (idWriteb,  idDisplayb)
               , (idWriteo,  idDisplayo)
               , (idWriteh,  idDisplayh)
               , (idFWrite,  idFDisplay)
               , (idFWriteb, idFDisplayb)
               , (idFWriteo, idFDisplayo)
               , (idFWriteh, idFDisplayh)
               ]

fromDisplayIdMap :: [(Id, Id)]
fromDisplayIdMap =
    let flip (a,b) = (b,a)
    in map flip toDisplayIdMap

-- #############################################################################
-- # Map to and from $display and $fdisplay etc.
-- #############################################################################

toFileId :: Id -> Id
toFileId id = case (LM.lookupBy qualEq toFileIdMap id) of
            Just x -> x
            _      -> internalError $ "ForeignFunctions: (toFileId) No FileId exists for " ++ (ppReadable id)


fromFileId :: Id -> Id
fromFileId id = case (LM.lookupBy qualEq fromFileIdMap id) of
              Just x -> x
              _      -> internalError $ "ForeignFunctions: (fromFileId) " ++ (ppReadable id) ++ "is not an FileId"

isFileId :: Id -> Bool
isFileId id = case (LM.lookupBy qualEq fromFileIdMap id) of
            Nothing -> False
            _       -> True

toFileIdMap :: [(Id, Id)]
toFileIdMap = [  (idWrite,   idFWrite)
               , (idWriteb,  idFWriteb)
               , (idWriteo,  idFWriteo)
               , (idWriteh,  idFWriteh)
               , (idDisplay,  idFDisplay)
               , (idDisplayb, idFDisplayb)
               , (idDisplayo, idFDisplayo)
               , (idDisplayh, idFDisplayh)
               ]

fromFileIdMap :: [(Id, Id)]
fromFileIdMap =
    let flip (a,b) = (b,a)
    in map flip toFileIdMap
