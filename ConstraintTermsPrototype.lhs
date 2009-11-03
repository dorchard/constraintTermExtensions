> module Main where

> import Language.Haskell.Meta.Parse
> import Language.Haskell.Exts.Extension
> import Language.Haskell.Exts.Fixity
> import Language.Haskell.Exts.Syntax
> import Language.Haskell.Exts.Parser

> import System.Environment

> import Rewrite.Synonyms
> import Rewrite.Families
> import Rewrite.PreTransform

> transform = rewriteFamilies . rewriteSynonyms

> preTransform = preTransformFamilies . preTransformSynonyms

> main = do
>   xs <- getArgs
>   case xs of
>     [] -> putStr usageMessage
>     [x] -> mainB x
>     [x,y] -> mainA x y
>     otherwise -> putStr usageMessage

> mainA inFile outFile = do
>   input <- readFile inFile
>   parsed <- return $ myParseHsModule (preTransform input)
>   case parsed of
>      Left err -> print err
>      Right x -> writeFile outFile (header ++ (pprHsModule (transform x)))

> mainB inFile = do
>   input <- readFile inFile
>   parsed <- return $ myParseHsModule (preTransform input)
>   case parsed of
>      Left err -> print err
>      Right x -> putStr $ (header ++ (pprHsModule $ transform x) ++ "\n\n")

> myParseMode :: ParseMode
> myParseMode = ParseMode
>  {parseFilename = [],
>   extensions = myExtensions,
>   ignoreLanguagePragmas = False,
>   fixities = baseFixities}

> myExtensions :: [Extension]
> myExtensions = [PostfixOperators,
>                 QuasiQuotes,
>                 UnicodeSyntax,
>                 PatternSignatures,
>                 MagicHash,
>                 ForeignFunctionInterface,
>                 TemplateHaskell,
>                 RankNTypes,
>                 MultiParamTypeClasses,
>                 RecursiveDo,
>                 TypeFamilies,
>                 KindSignatures,
>                 FlexibleContexts]

                 ScopedTypeVariables

> myParseHsModule :: String -> Either String Module
> myParseHsModule = parseResultToEither . parseModuleWithMode myParseMode

> header = "{-# LANGUAGE TypeFamilies #-}\n{-# LANGUAGE GADTs #-}\n\n"

> usageMessage = "usage:\t constraintTermExts input.hs output.hs\n or"++
>                 "\t constraintTermExts input.hs\n\n"