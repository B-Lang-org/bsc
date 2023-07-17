module VPIWrappers ( genVPIWrappers, genVPIRegistrationArray ) where

import ForeignFunctions
import CCSyntax
import Id (getIdString)
import Error(ErrorHandle)
import Flags(Flags(..), quiet)
import FileNameUtil(mkVPICName, mkVPIHName, mkVPIArrayCName,
                    getRelativeFilePath, dropSuf, baseName)
import AVerilogUtil(vNameToTask)
import FileIOUtil(writeFileCatch)
import PPrint (ppReadable)
import TopUtils(putStrLnF, commentC)
import Data.List(genericLength)

import Control.Monad(unless)

--import Debug.Trace

genVPIWrappers :: ErrorHandle ->
                  Flags -> String -> [String] -> [ForeignFunction] ->
                  IO [CCFragment]
genVPIWrappers errh flags prefix blurb ffs =
  do files <- mapM (writeWrapper errh flags prefix blurb) ffs
     return $ concat files

writeWrapper :: ErrorHandle ->
                Flags -> String -> [String] -> ForeignFunction ->
                IO [CCFragment]
writeWrapper errh flags prefix blurb ff =
  do let function_name = getIdString (ff_name ff)

         -- generate the wrapper file names
         c_filename = mkVPICName (vdir flags) prefix function_name
         h_filename = mkVPIHName (vdir flags) prefix function_name
         h_filename_rel = getRelativeFilePath h_filename

         -- generate the wrapper file contents
         reg_array = mkVPIRegistrationArray flags prefix [ff] False
         registration_hint =
           [ "To automatically register this VPI wrapper with a Verilog simulator use:" ] ++
           (map ("    "++) (lines (ppReadable reg_array)))

         has_return = (isNarrow (ff_ret ff)) || (isWide (ff_ret ff))
         return_size = case (ff_ret ff) of
                         (Narrow n) -> n
                         (Wide n)   -> n
                         _          -> 0

         stores_handles = not (null (ff_args ff) && (isAbsent (ff_ret ff)))

         tab_line = (vNameToTask False function_name) ++
                    " call=" ++ function_name ++ "_calltf" ++
                    " size=" ++ (show return_size) ++
                    " acc=rw:%TASK"
         tab_hint =
           [ ""
           , "For a Verilog simulator which requires a .tab file, use the following entry:"
           , tab_line
           ]

         sft_line = (vNameToTask False function_name) ++
                    " vpiSysFuncSized " ++ (show return_size) ++
                    " unsigned"
         sft_hint =
           [ ""
           , "For a Verilog simulator which requires a .sft file, use the following entry:"
           , sft_line
           ]

         header = blurb ++ registration_hint ++
                  if has_return then (tab_hint ++ sft_hint) else []

         calltf_fn_type = mkVPIWrapperType function_name
         calltf_fn_body = mkVPIWrapperBody function_name ff

         sizetf_fn_type = mkVPISizeType function_name
         sizetf_fn_body = mkVPISizeBody ff

         register_fn_type = mkVPIRegisterType function_name
         register_fn_body = mkVPIRegisterBody function_name has_return stores_handles

         c_segments = [ cpp_system_include "stdlib.h"
                      , cpp_system_include "vpi_user.h"
                      , cpp_include "bdpi.h"
                      , comment "the type of the wrapped function"
                                (mkFFDecl ff)
                      , comment "VPI wrapper function"
                                (define calltf_fn_type calltf_fn_body)
                      ] ++
                      (if has_return
                       then [ literal_comment ["sft: " ++ sft_line]
                            , literal_comment ["tab: " ++ tab_line]
                            , blankLines 1
                            , define sizetf_fn_type sizetf_fn_body
                            ]
                       else [])
                        ++
                      [ comment "VPI wrapper registration function"
                                (define register_fn_type register_fn_body)
                      ]
         c_contents = (commentC header) ++
                      (ppReadable (program c_segments))

         -- generate the wrapper header contents
         h_segments = [ cpp_system_include "vpi_user.h"
                      , comment "registration function"
                          (decl register_fn_type)
                      , comment "VPI wrapper function"
                          (decl calltf_fn_type)
                      ]
         h_file_tag = dropSuf (baseName h_filename)
         h_contents = (commentC blurb) ++
                      (ppReadable (protect_header h_file_tag h_segments))

     -- write the file contents
     writeFileCatch errh c_filename c_contents
     writeFileCatch errh h_filename h_contents
     -- report the file to the user with relative path
     unless (quiet flags) $ putStrLnF $ "VPI wrapper files created: " ++
                                        (dropSuf h_filename_rel) ++ ".{c,h}"
     -- return the file contents for dumping purposes
     return $ h_segments ++ c_segments

mkVPIWrapperType :: String -> CCFragment
mkVPIWrapperType name =
  let wrapper_name = name ++ "_calltf"
  in function (userType "PLI_INT32") (mkVar wrapper_name) [ decl $ (ptr . (userType "PLI_BYTE8")) (mkVar "user_data") ]

mkVPIWrapperBody :: String -> ForeignFunction -> CCFragment
mkVPIWrapperBody name ff =
  let numbered_args = zip [(1::Integer)..] (ff_args ff)
      rt = ff_ret ff
      num_rets = if (isAbsent rt) then 0 else 1
      num_hdls = (genericLength numbered_args) + num_rets
      locals = if (num_hdls > 0)
               then [ decl $ (userType "vpiHandle") (mkVar "hCall") ]
               else []
      arg_locals = if null numbered_args
                   then []
                   else concatMap declArg numbered_args
      ret_locals = if isAbsent rt
                   then []
                   else [ decl $ (ftType rt) (mkVar "vpi_result") ]
      hdl_array = if (num_hdls > 0)
                  then [ decl $ (ptr . (userType "vpiHandle")) (mkVar "handle_array") ]
                  else []
      alloc_handles = block $ [ decl $ (userType "vpiHandle") (mkVar "hArgList")
                              , (mkVar "hArgList") `assign`
                                   ((var "vpi_iterate") `cCall` [ var "vpiArgument"
                                                                , var "hCall" ])
                              , (mkVar "handle_array") `assign`
                                   ((var "malloc") `cCall` [ ((var "sizeof") `cCall` [var "vpiHandle"]) `cMul` (mkUInt32 num_hdls) ])
                              ] ++
                              (if (num_rets == 1)
                               then let rhs = if (isPoly rt)
                                              then ((var "vpi_scan") `cCall` [ var "hArgList" ])
                                              else (var "hCall")
                                    in [(stmt ((var "handle_array") `cIndex` (mkUInt32 0))) `assign` rhs]
                               else []) ++
                              (concatMap (initArgHdl num_rets) numbered_args) ++
                              [ stmt $ (var "vpi_put_userdata") `cCall` [ var "hCall", var "handle_array" ]
                              , stmt $ (var "vpi_free_object") `cCall` [ var "hArgList" ]
                              ]
      handles = if (num_hdls > 0)
                then [ comment "retrieve handle array" (blankLines 0)
                     , (mkVar "hCall") `assign`
                          ((var "vpi_handle") `cCall` [ var "vpiSysTfCall"
                                                      , mkSInt32 0 ])
                     , (mkVar "handle_array") `assign`
                          ((var "vpi_get_userdata") `cCall` [var "hCall"])
                     , if_cond ((var "handle_array") `cEq` mkNULL) alloc_handles Nothing
                     ]
                else []
      ret_handle = if (isAbsent rt)
                   then []
                   else [ comment "create return value" (blankLines 0)
                        , stmt $ (var "make_vpi_result") `cCall`
                                   [ (var "handle_array") `cIndex` (mkUInt32 0)
                                   , cAddr (var "vpi_result")
                                   , if isPoly rt
                                     then var "POLYMORPHIC"
                                     else var "DIRECT"
                                   ]
                        ]
      args    = case numbered_args of
                  [] -> []
                  as -> [ comment "copy in argument values" (blankLines 0) ] ++
                        (concatMap (copyArg num_rets) as)
      call    = [ comment "call the imported C function" (blankLines 0)
                , mkCall name rt numbered_args
                ]
      ret_val = if isAbsent rt
                then []
                else [ comment "copy out return value" (blankLines 0)
                     , stmt $ (var "put_vpi_result") `cCall`
                                 [ (var "handle_array") `cIndex` (mkUInt32 0)
                                 , cAddr (var "vpi_result")
                                 , if isPoly rt
                                   then var "POLYMORPHIC"
                                   else var "DIRECT"
                                 ]
                     ]
      free_args = case numbered_args of
                  [] -> []
                  as -> [ comment "free argument storage" (blankLines 0)
                        , stmt $ (var "free_vpi_args") `cCall` []
                        ]
      free_hdls = if (num_hdls > 0)
                  then [ stmt $ (var "vpi_free_object") `cCall` [ var "hCall" ] ]
                  else []
      exit    = [ blankLines 1, ret (Just (mkSInt32 0)) ]
  in block $ locals ++
             arg_locals ++
             ret_locals ++
             hdl_array ++
             handles ++
             ret_handle ++
             args ++
             call ++
             ret_val ++
             free_args ++
             free_hdls ++
             exit
  where declArg (n,ft) =
          [ decl $ (ftType ft) (mkVar (argName n)) ]
        initArgHdl nr (n,ft) =
          [ (stmt ((var "handle_array") `cIndex` (mkUInt32 (n-1+nr)))) `assign`
                ((var "vpi_scan") `cCall` [ var "hArgList" ])
          ]
        copyArg nr (n,ft) =
          [ stmt $ (var "get_vpi_arg") `cCall` [ (var "handle_array") `cIndex` (mkUInt32 (n-1+nr))
                                               , cAddr (var (argName n))
                                               , if isPoly ft
                                                 then var "POLYMORPHIC"
                                                 else if isString ft
                                                      then var "STRING"
                                                      else var "DIRECT"
                                               ]
          ]
        ftType Void = void
        ftType (Narrow n) | n <= 8    = char
                          | n <= 32   = unsigned . int
                          | otherwise = unsigned . long
        ftType (Wide n)    = ptr . unsigned . int
        ftType Polymorphic = ptr . unsigned . int
        ftType StringPtr   = ptr . char
        argName n = "arg_" ++ (show n)
        mkCall name rt args =
          let arg_list = [ var (argName n) | (n,_) <- args ]
          in if isAbsent rt || isWide rt || isPoly rt
             then let arg_list' = if isAbsent rt
                                  then arg_list
                                  else ((var "vpi_result"):arg_list)
                  in stmt $ (var name) `cCall` arg_list'
             else (mkVar "vpi_result") `assign` ((var name) `cCall` arg_list)

mkVPISizeType :: String -> CCFragment
mkVPISizeType name =
  let wrapper_name = name ++ "_sizetf"
  in function (userType "PLI_INT32") (mkVar wrapper_name) [ decl $ (ptr . (userType "PLI_BYTE8")) (mkVar "user_data") ]

mkVPISizeBody :: ForeignFunction -> CCFragment
mkVPISizeBody ff =
  case ff_ret ff of
    (Narrow n) -> block [ ret (Just (mkUInt32 n)) ]
    (Wide n)   -> block [ ret (Just (mkUInt32 n)) ]
    _          -> block []

regRoutineType :: CCFragment -> CCFragment
regRoutineType v = function void v []

mkVPIRegisterType :: String -> CCFragment
mkVPIRegisterType name = regRoutineType (mkVar (name ++ "_vpi_register"))

mkVPIRegisterBody :: String -> Bool -> Bool -> CCFragment
mkVPIRegisterBody name has_return stores_handles =
  let assignField f e = stmt ((var "tf_data") `cDot` f) `assign` e
  in block $ [ decl . (userType "s_vpi_systf_data") $ (mkVar "tf_data")
             , comment "Fill in registration data" (blankLines 0)
             ] ++
             (if has_return
              then [ assignField "type"        (var "vpiSysFunc")
                   , assignField "sysfunctype" (var "vpiSizedFunc")
                   ]
              else [ assignField "type" (var "vpiSysTask") ])
               ++
             [ assignField "tfname"    (mkStr (vNameToTask False name))
             , assignField "calltf"    (var (name ++ "_calltf"))
             , assignField "compiletf" (mkUInt32 0)
             ] ++
             (if has_return
              then [ assignField "sizetf" (var (name ++ "_sizetf")) ]
              else [ assignField "sizetf" (mkUInt32 0) ])
               ++
             [ assignField "user_data" (mkStr (vNameToTask False name))
             , comment "Register the function with VPI" (blankLines 0)
             , stmt $ (var "vpi_register_systf") `cCall` [cAddr (var "tf_data")]
             ]

genVPIRegistrationArray :: ErrorHandle ->
                           Flags -> String -> [String] -> [ForeignFunction] ->
                           IO [String]
genVPIRegistrationArray _ _ _ _ [] = return []
genVPIRegistrationArray errh flags prefix blurb ffs =
  do let -- generate the registration array file name
         c_filename = mkVPIArrayCName (vdir flags) prefix
         c_filename_rel = getRelativeFilePath c_filename

         -- generate the resitration array file contents
         reg_array = mkVPIRegistrationArray flags prefix ffs True
         c_contents = (commentC blurb) ++
                      (ppReadable (comment "registration array" reg_array))

     -- write the file contents
     writeFileCatch errh c_filename c_contents
     -- report the file to the user with relative path
     unless (quiet flags) $ putStrLnF $ "VPI registration array file created: " ++ c_filename_rel
     -- return the file name
     return [c_filename]

mkVPIRegistrationArray :: Flags -> String -> [ForeignFunction] -> Bool -> CCFragment
mkVPIRegistrationArray flags prefix ffs with_fn =
  let names         = [ getIdString (ff_name ff) | ff <- ffs ]
      include_files = map (mkVPIHName (vdir flags) prefix) names
      reg_fn_type   = regRoutineType (mkVar "vpi_register_all")
      reg_fn_body   =
        block [ stmt $ (var (name ++ "_vpi_register")) `cCall` []
              | name <- names ]
      reg_fn        =
        if with_fn
        then [comment "Convenience function to register all imported functions"
                (define reg_fn_type reg_fn_body)]
        else []

      noret_names =
        map (getIdString . ff_name) $
          filter (\ff->not (isNarrow (ff_ret ff) || isWide (ff_ret ff))) ffs
      reg_fn2_type = regRoutineType (mkVar "vpi_register_tasks")
      reg_fn2_body =
        block [ stmt $ (var (name ++ "_vpi_register")) `cCall` []
              | name <- noret_names ]
      reg_fn2      =
        if with_fn
        then [comment "Convenience function to register only tasks"
                (define reg_fn2_type reg_fn2_body)]
        else []

      array_name       = "vlog_startup_routines"
      array_values     = if with_fn
                         then [ var ("vpi_register_all"), mkUInt32 0 ]
                         else [ var (name ++ "_vpi_register")
                              | name <- names ] ++
                              [ mkUInt32 0 ]
      initializer      = mkInitBraces array_values
      array_decl       = decl $ array . ptr . regRoutineType $
                             (mkVar array_name) `assign` initializer
  in program $ [ cpp_include (baseName f) | f <- include_files ] ++
               reg_fn ++ reg_fn2 ++ [ array_decl ]
