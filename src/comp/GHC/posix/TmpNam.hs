module TmpNam(tmpNam) where
import System.Posix

tmpNam :: IO String
tmpNam = do
         x <- getProcessID
         return $ "/tmp/bsc" ++ show x
