Author: Dominic Orchard
License: BSD

Prototype implementation of constraint synonsm and constraint families as described in
"Haskell Type Constraints Unleashed" (Dominic Orchard, Tom Schrijvers)

> module Rewrite.Synonyms(rewriteSynonyms) where
>
> import Language.Haskell.Exts.Syntax
>
> import Rewrite.Helpers

> rewriteSynonyms (Module srcLoc moduleName opts warning exports imports decls) =
>         Module srcLoc moduleName opts warning exports imports (process decls)

> process = (correctLineNumbers 0) . (concatMap processDecls)

processDecls: processes all declarations in a module, converting
constraint synonyms (that look like functions) to their class/instance encoding
                       
> processDecls (FunBind [Match s (Ident "constraint") pats
>                        typ (UnGuardedRhs rhs) binds]) = 
>     case pats of
>       (((PApp (UnQual (Ident name)) ps1)):ps2) ->
>           
>           [(ClassDecl s context (Ident name)
>            (map convertToClassParams (ps1++ps2)) [] [], 0),
>            (InstDecl s context (UnQual $ Ident name)
>             (map convertToInstanceParams (ps1++ps2)) [],1)]
>           where
>             context = interpretValueAsConstraint rhs
>           
>       otherwise -> error "Constraint synonym is malformed in RHS"

> processDecls (FunBind (x@(Match s (Ident "constraint") pats
>                        typ (UnGuardedRhs rhs) binds):xs)) = 
>      (processDecls (FunBind [x]))++(processDecls (FunBind xs))
>     

> processDecls x = [(x, 0)]

convertToClassParams: interpret function paramters as class parameters

> convertToClassParams (PVar x) = UnkindedVar x
> convertToClassParams _ = error "Constraint synonym is malformed in parameters"

convertToInstanceParams: interpret function parameters as instance parameters

> convertToInstanceParams (PVar x) = TyVar x
> convertToInstanceParams _ = error "Constraint synonym is malformed in parameters"
