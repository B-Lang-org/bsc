module ErrorUtil (internalError) where

-- import Pretty	-- causes loops
import System.IO(hPutStr, stderr)
import System.IO.Unsafe(unsafePerformIO)
import System.Exit(exitWith, ExitCode(..))

import Version(version)

{-# NOINLINE internalError #-}
--
-- This module contains very basic *internal* error facilities,
-- so that packages such as Util and IntegerUtil can use basic
-- error functions, while Error can import those packages without
-- circular dependency.
--

-- This is called from anywhere, even when not in the IO monad
internalError = unsafePerformIO . safeInternalError

safeInternalError :: String -> IO a
safeInternalError msg_data =
    let title = "Internal Bluespec Compiler Error"
        desc1 = "Please report this failure to your Bluespec technical contact.\n" ++
                 "If you do not know your contact, you may email support@bluespec.com.\n"
        desc2 = "The following internal error message should be included in your\n" ++
                "correspondence along with any other relevant details:\n"
        ver = version ++ "\n"
{- pretty-printing causes reference loops here.
        msg_doc = (text title) <> (char ':') $$
                  nest 2 ((s2par desc1) $$
                          (s2par desc2) $$
                          nest 2 (s2par msg_data))
        msg_str = pretty 78 78 msg_doc
 -}
        msg_str = title ++ ":\n" ++ desc1 ++ desc2 ++ ver ++ msg_data ++ "\n"
    in
        hPutStr stderr msg_str >>
        exitWith (ExitFailure 1)
