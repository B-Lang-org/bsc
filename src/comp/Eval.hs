module Eval(NFData(..), deepseq,
            rnf2, rnf3, rnf4, rnf5, rnf6, rnf7, rnf8, rnf9,
            rnf10, rnf11, rnf12, rnf13, rnf14, rnf15, rnf16,
            rnf17, rnf18, rnf19,
            rnfId) where

import Control.DeepSeq(NFData(..), deepseq)
import System.IO(Handle)
import FStringCompat(FString)

-- NFData instances for basic types not provided by deepseq

instance NFData Handle where
    rnf x = seq x ()

instance NFData FString where
    rnf x = seq x ()

-- Helper functions for deep evaluation of multiple arguments
rnf2 :: (NFData a1, NFData a2) => a1 -> a2 -> ()
rnf2 x1 x2 = rnf x1 `seq` rnf x2 `seq` ()

rnf3 :: (NFData a1, NFData a2, NFData a3) => a1 -> a2 -> a3 -> ()
rnf3 x1 x2 x3 = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` ()

rnf4 :: (NFData a1, NFData a2, NFData a3, NFData a4)
       => a1 -> a2 -> a3 -> a4 -> ()
rnf4 x1 x2 x3 x4 = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` ()

rnf5 :: (NFData a1, NFData a2, NFData a3, NFData a4, NFData a5)
       => a1 -> a2 -> a3 -> a4 -> a5 -> ()
rnf5 x1 x2 x3 x4 x5 =
   rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` rnf x5 `seq` ()

rnf6 :: (NFData a1, NFData a2, NFData a3, NFData a4, NFData a5, NFData a6)
       => a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> ()
rnf6 x1 x2 x3 x4 x5 x6 =
    rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` rnf x5 `seq` rnf x6 `seq` ()

rnf7 :: (NFData a1, NFData a2, NFData a3, NFData a4, NFData a5, NFData a6, NFData a7)
       => a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> ()
rnf7 x1 x2 x3 x4 x5 x6 x7 =
    rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` rnf x5 `seq` rnf x6 `seq` rnf x7
       `seq` ()

rnf8 :: (NFData a1, NFData a2, NFData a3, NFData a4, NFData a5, NFData a6, NFData a7
          ,NFData a8) => a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> a8 -> ()
rnf8 x1 x2 x3 x4 x5 x6 x7 x8 =
    rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` rnf x5 `seq` rnf x6 `seq` rnf x7
       `seq` rnf x8 `seq` ()

rnf9 :: (NFData a1, NFData a2, NFData a3, NFData a4, NFData a5, NFData a6, NFData a7
          ,NFData a8, NFData a9)
       => a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> a8 -> a9 -> ()
rnf9 x1 x2 x3 x4 x5 x6 x7 x8 x9 =
    rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` rnf x5 `seq` rnf x6 `seq` rnf x7
       `seq` rnf x8 `seq` rnf x9 `seq` ()

rnf10 :: (NFData a1, NFData a2, NFData a3, NFData a4, NFData a5, NFData a6, NFData a7
           ,NFData a8, NFData a9, NFData a10)
       => a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> a8 -> a9 -> a10 -> ()
rnf10 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 =
    rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` rnf x5 `seq` rnf x6 `seq` rnf x7
       `seq` rnf x8 `seq` rnf x9 `seq` rnf x10 `seq` ()

rnf11 :: (NFData a1, NFData a2, NFData a3, NFData a4, NFData a5, NFData a6, NFData a7
           ,NFData a8, NFData a9, NFData a10, NFData a11)
       => a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> a8 -> a9 -> a10 -> a11
       -> ()
rnf11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 =
    rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` rnf x5 `seq` rnf x6 `seq` rnf x7
       `seq` rnf x8 `seq` rnf x9 `seq` rnf x10 `seq` rnf x11 `seq` ()

rnf12 :: (NFData a1, NFData a2, NFData a3, NFData a4, NFData a5, NFData a6, NFData a7
           ,NFData a8, NFData a9, NFData a10, NFData a11, NFData a12)
       => a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> a8 -> a9 -> a10 -> a11
       -> a12 -> ()
rnf12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 =
    rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` rnf x5 `seq` rnf x6 `seq` rnf x7
       `seq` rnf x8 `seq` rnf x9 `seq` rnf x10 `seq` rnf x11 `seq` rnf x12 `seq` ()

rnf13 :: (NFData a1, NFData a2, NFData a3, NFData a4, NFData a5, NFData a6, NFData a7
           ,NFData a8, NFData a9, NFData a10, NFData a11, NFData a12, NFData a13)
       => a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> a8 -> a9 -> a10 -> a11
       -> a12 -> a13 -> ()
rnf13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 =
    rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` rnf x5 `seq` rnf x6 `seq` rnf x7
       `seq` rnf x8 `seq` rnf x9 `seq` rnf x10 `seq` rnf x11 `seq` rnf x12 `seq` rnf x13
       `seq` ()

rnf14 :: (NFData a1, NFData a2, NFData a3, NFData a4, NFData a5, NFData a6, NFData a7
           ,NFData a8, NFData a9, NFData a10, NFData a11, NFData a12, NFData a13
           ,NFData a14)
       => a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> a8 -> a9 -> a10 -> a11
       -> a12 -> a13 -> a14 -> ()
rnf14 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 =
    rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` rnf x5 `seq` rnf x6 `seq` rnf x7
       `seq` rnf x8 `seq` rnf x9 `seq` rnf x10 `seq` rnf x11 `seq` rnf x12 `seq` rnf x13
       `seq` rnf x14 `seq` ()

rnf15 :: (NFData a1, NFData a2, NFData a3, NFData a4, NFData a5, NFData a6, NFData a7
           ,NFData a8, NFData a9, NFData a10, NFData a11, NFData a12, NFData a13
           ,NFData a14, NFData a15)
       => a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> a8 -> a9 -> a10 -> a11
       -> a12 -> a13 -> a14 -> a15 -> ()
rnf15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 =
    rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` rnf x5 `seq` rnf x6 `seq` rnf x7
       `seq` rnf x8 `seq` rnf x9 `seq` rnf x10 `seq` rnf x11 `seq` rnf x12 `seq` rnf x13
       `seq` rnf x14 `seq` rnf x15 `seq` ()

rnf16 :: (NFData a1, NFData a2, NFData a3, NFData a4, NFData a5, NFData a6, NFData a7
           ,NFData a8, NFData a9, NFData a10, NFData a11, NFData a12, NFData a13
           ,NFData a14, NFData a15, NFData a16)
       => a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> a8 -> a9 -> a10 -> a11
       -> a12 -> a13 -> a14 -> a15 -> a16 -> ()
rnf16 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 =
    rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` rnf x5 `seq` rnf x6 `seq` rnf x7
       `seq` rnf x8 `seq` rnf x9 `seq` rnf x10 `seq` rnf x11 `seq` rnf x12 `seq` rnf x13
       `seq` rnf x14 `seq` rnf x15 `seq` rnf x16 `seq` ()

rnf17 :: (NFData a1, NFData a2, NFData a3, NFData a4, NFData a5, NFData a6, NFData a7
           ,NFData a8, NFData a9, NFData a10, NFData a11, NFData a12, NFData a13
           ,NFData a14, NFData a15, NFData a16, NFData a17)
       => a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> a8 -> a9 -> a10 -> a11
       -> a12 -> a13 -> a14 -> a15 -> a16 -> a17 ->  ()
rnf17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 =
    rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` rnf x5 `seq` rnf x6 `seq` rnf x7
       `seq` rnf x8 `seq` rnf x9 `seq` rnf x10 `seq` rnf x11 `seq` rnf x12 `seq` rnf x13
       `seq` rnf x14 `seq` rnf x15 `seq` rnf x16 `seq` rnf x17 `seq` ()

rnf18 :: (NFData a1, NFData a2, NFData a3, NFData a4, NFData a5, NFData a6, NFData a7
           ,NFData a8, NFData a9, NFData a10, NFData a11, NFData a12, NFData a13
           ,NFData a14, NFData a15, NFData a16, NFData a17, NFData a18)
       => a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> a8 -> a9 -> a10 -> a11
       -> a12 -> a13 -> a14 -> a15 -> a16 -> a17 -> a18 -> ()
rnf18 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 =
    rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` rnf x5 `seq` rnf x6 `seq` rnf x7
       `seq` rnf x8 `seq` rnf x9 `seq` rnf x10 `seq` rnf x11 `seq` rnf x12 `seq` rnf x13
       `seq` rnf x14 `seq` rnf x15 `seq` rnf x16 `seq` rnf x17 `seq` rnf x18 `seq` ()

rnf19 :: (NFData a1, NFData a2, NFData a3, NFData a4, NFData a5, NFData a6, NFData a7
           ,NFData a8, NFData a9, NFData a10, NFData a11, NFData a12, NFData a13
           ,NFData a14, NFData a15, NFData a16, NFData a17, NFData a18, NFData a19)
       => a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> a8 -> a9 -> a10 -> a11
       -> a12 -> a13 -> a14 -> a15 -> a16 -> a17 -> a18 -> a19 -> ()
rnf19 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 =
    rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` rnf x5 `seq` rnf x6 `seq` rnf x7
       `seq` rnf x8 `seq` rnf x9 `seq` rnf x10 `seq` rnf x11 `seq` rnf x12 `seq` rnf x13
       `seq` rnf x14 `seq` rnf x15 `seq` rnf x16 `seq` rnf x17 `seq` rnf x18 `seq` rnf x19
       `seq` ()

rnfId :: NFData a => a -> a
rnfId x = rnf x `seq` x
