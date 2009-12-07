Author: Dominic Orchard
License: BSD

Prototype implementation of constraint synonsm and constraint families as described in
"Haskell Type Constraints Unleashed" (Dominic Orchard, Tom Schrijvers)

> module Main where

> import Language.Haskell.Meta.Parse
> import Language.Haskell.Exts.Fixity
> import Language.Haskell.Exts.Syntax
> import Language.Haskell.Exts.Parser

> import System.Environment

 import System.IO

> import Rewrite.Helpers
> import Rewrite.Synonyms
> import Rewrite.Families
> import Rewrite.PreTransform

> transform = rewriteFamilies . rewriteSynonyms

> preTransform = preTransformFamilies . preTransformSynonyms

> main = do
>   xs <- getArgs
>   case xs of
>     [x] -> mainB x
>     [x,y] -> mainA x y
>     [x,y,z] -> mainA y z
>     otherwise -> putStr usageMessage

> mainC input =
>     case myParseHsModule (preTransform input) of
>          Left err -> print err
>          Right x -> putStr $ (header ++ (pprHsModule $ transform x) ++ "\n\n")

> mainA inFile outFile = do
>   input <- readFile inFile
>   parsed <- return $ myParseHsModule (preTransform input)
>   case parsed of
>      Left err -> print err
>      Right x -> writeFile outFile (header ++ (pprHsModule $ transform x))

> mainB inFile = do
>   input <- readFile inFile
>   parsed <- return $ myParseHsModule (preTransform input)
>   case parsed of
>      Left err -> print err
>      Right x -> putStr $ (header ++ (pprHsModule $ transform x) ++ "\n\n")

> header = concatMap (\x -> "{-#"++x++"#-}\n") ["FlexibleContexts",
>                                               "FlexibleInstances",
>                                               "UndecidableInstances",
>                                               "TypeFamilies",
>                                               "GADTs"]
>                                         

> usageMessage = "usage:\t constraintTermExts input.hs output.hs\n or"++
>                 "\t constraintTermExts input.hs\n\n"