> module Rewrite.PreTransform where

> import Text.ParserCombinators.Parsec
> import Text.ParserCombinators.Parsec.Expr
> import qualified Text.ParserCombinators.Parsec.Token as Token
> import Text.ParserCombinators.Parsec.Language

> preTransformSynonyms = id

preTransformFamilies: converts "constraint family" into "type family" and
"constraint instance" into "type instance" prefixing familynames with
"ConstraintFamily" to be picked up by the main transformation process

> preTransformFamilies input =
>    case (parse hsparse "" (input++"\n")) of
>            Left err -> error $ "Malformed constraint families:"++(show err)
>            Right x -> concat x

> hsline = do { try constraintFamilies } <|>
>          do { try constraintInstances } <|>
>          parseUntil '\n'

> hsparse = do
>   lines <- many hsline 
>   eof
>   return lines

> constraintFamilies = do
>   reserved "constraint"
>   reserved "family"
>   c <- constructor
>   rest <- parseUntil '\n'
>   return $ "type family ConstFam"++c++" "++rest

> constraintInstances = do
>   reserved "constraint"
>   reserved "instance"
>   c <- constructor
>   rest <- parseUntil '\n'
>   return $ "type instance ConstFam"++c++" "++rest

> lexer :: Token.TokenParser ()
> lexer = Token.makeTokenParser
>         (haskellDef
>          { reservedNames = ["constraint", "family", "instance"]
>           })

> reserved = Token.reserved lexer
> lexeme = Token.lexeme lexer
> natural = Token.natural lexer
> whiteSpace = Token.whiteSpace lexer
> idchar = lower <|> upper <|> digit <|> char '_'
> constructor = lexeme $ do { c <- upper; cs <- many idchar; return (c:cs) }

> parseUntil c = do
>     c' <- anyChar
>     if (c'==c) then return [c]
>       else do 
>          cs <- parseUntil c
>          return (c':cs)