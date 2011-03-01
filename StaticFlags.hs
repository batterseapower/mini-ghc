module StaticFlags where

import System.Environment
import System.IO.Unsafe


{-# NOINLINE aSSERTIONS #-}
aSSERTIONS :: Bool
aSSERTIONS = not $ "--no-assertions" `elem` unsafePerformIO getArgs

{-# NOINLINE qUIET #-}
qUIET :: Bool
qUIET = "-v0" `elem` unsafePerformIO getArgs
