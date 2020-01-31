module BinaryIO(writeBinaryFile, readBinaryFile) where
import System.IO

writeBinaryFile :: FilePath -> String -> IO ()
writeBinaryFile name str = do
  hdl <- openBinaryFile name WriteMode
  hPutStr hdl str
  hClose hdl

readBinaryFile :: FilePath -> IO String
readBinaryFile name = do
  hdl <- openBinaryFile name ReadMode
  hGetContents hdl
