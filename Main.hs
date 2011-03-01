module Main where

import Core.Parser
import Core.Infer

import System.Environment

import Utilities


main = do
    [fp] <- getArgs
    xes <- parse fp
    case infer xes of
        Right xes -> print $ pPrint xes
        Left err  -> putStrLn err
