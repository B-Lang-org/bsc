module TmpNam(tmpNam, localTmpNam) where
import System.Posix

tmpNam :: IO String
tmpNam = do
         x <- localTmpNam
         return $ "/tmp/bsc" ++ x

localTmpNam :: IO String
localTmpNam = do
         x <- getProcessID
         return $ show x
