module Main where
import Control.Monad (unless)
import ABin
import ASyntax
import GenABin (readABinFile)
import Error (initErrorHandle)
import qualified Data.ByteString as B
import qualified Data.Map as M
import System.Environment (getArgs)
import System.FilePath ((</>))

main = do
    [mode,dir] <- getArgs
    mapM_ (check mode dir) ["mkDeclaredByteSink","mkDeclaredOnlyTypes"]
  where
    check mode dir modName = do
        bytes <- B.readFile (dir </> modName ++ ".ba")
        errh <- initErrorHandle
        let (ABinMod info _,_) = readABinFile errh (dir </> modName ++ ".ba") bytes
            pkg = abmi_apkg info
        unless (null (apkg_expr_types pkg)) $
            error "fixture unexpectedly contains expression type observations"
        if mode == "sim" || mode == "staged"
          then unless (apkg_final_wire_names pkg == Nothing &&
                       apkg_final_wire_types pkg == Nothing) $
                   error "pre-codegen package unexpectedly has final physical metadata"
          else do
            unless (apkg_final_wire_types pkg == Just M.empty) $
                error "declared-only fixture should have an authoritative empty inferred cache"
            let pairs = if modName == "mkDeclaredOnlyTypes"
                        then [("sink$get","sink_get"),("sink$EN_put","sink_EN_put"),
                              ("sink$put_payload","sink_1put_payload"),
                              ("sink_put_payload","sink_put_payload")]
                        else [("value$D_IN","value_D_IN"),("value$EN","value_EN")]
                expected = [(old,if mode == "dollar" then new else old) | (old,new) <- pairs]
            case apkg_final_wire_names pkg of
              Just names -> mapM_ (\(old,new) -> unless (M.lookup old names == Just new) $
                  error ("missing exact emitted binding: " ++ show (old,new,M.lookup old names))) expected
              Nothing -> error "Verilog package has no final-name map"
        putStrLn ("PASS: " ++ mode ++ " " ++ modName ++ " has no observations and correct final metadata")
