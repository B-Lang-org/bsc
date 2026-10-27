{-# LANGUAGE CPP #-}
-- The object format of the host: GHC defines the host OS macro.
module BuildSystem (BinFmtType(..), getBinFmtType) where

import Warmup ()

data BinFmtType = ELF | MachO

getBinFmtType :: BinFmtType
#if defined(darwin_HOST_OS)
getBinFmtType = MachO
#else
getBinFmtType = ELF
#endif
