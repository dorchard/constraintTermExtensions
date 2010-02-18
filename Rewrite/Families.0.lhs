> module Rewrite.Families where
>
> import Language.Haskell.Meta
> import Language.Haskell.Exts.Syntax

> import Rewrite.Helpers

> rewriteFamilies (Module srcLoc moduleName opts warning exports imports decls) =
>         Module srcLoc moduleName opts warning exports imports (process decls)

> process ds = correctLineNumbers 0 (processDecls ds 0)
>          where
>            processDecls [] _ = []
>            processDecls (d:ds) fresh = 
>                       let (ds', fresh') = processDecls' d fresh
>                       in  ds'++(processDecls ds fresh')

SrcLoc Name [TyVarBind] (Maybe Kind)

Type families are left as is 

> processDecls' (TypeFamDecl s (Ident name) params kind) fresh =
>     ([(TypeFamDecl s (Ident name) params kind), 0], fresh)

> processDecls' (TypeInsDecl s t1 t2) fresh = 
>     let
>       consName = Ident $ "ND"++(show fresh)
>       dictName = Ident $ "Dict"++(show fresh)
>       params = getVariables t1
>       gadtParams = map UnkindedVar params
>       gadtType = tyApp (TyCon (UnQual dictName)) params
>       famInstance = TypeInsDecl s t1 gadtType
>       gadt = GDataDecl s DataType [] dictName gadtParams Nothing [decl] []
>       constraint = interpretTypeAsConstraint t2
>       decl = GadtDecl s consName (TyForall Nothing constraint gadtType)
>     in
>       ([(famInstance, 0), (gadt, 1)], fresh+1)
> processDecls' x f = ([(x, 0)], f)


tyApp: given a constructor and a list of identifies, create a nested
application term of variables to the constructor

> tyApp con is = tyApp' con (reverse is)
> tyApp' con [] = con
> tyApp' con [i] = TyApp con (TyVar i)
> tyApp' con (i:is) = TyApp (tyApp' con is) (TyVar i)


getVariables extracts just the type variables from a type
Used to find get the required maximum number of parameters required for a 
GADT encoding a constraint family instance

> getVariables (TyFun t1 t2) = getVariables t1 ++ getVariables t2
> getVariables (TyTuple _ ts) = concatMap getVariables ts
> getVariables (TyList t) = getVariables t
> getVariables (TyApp t1 t2) = getVariables t1 ++ getVariables t2
> getVariables (TyVar (Ident a)) = [Ident a]
> getVariables (TyParen t) = getVariables t
> getVariables (TyInfix t1 _ t2) = getVariables t1 ++ getVariables t2
> getVariables (TyKind t _) = getVariables t
> getVariables (TyCon _) = []
> getVariables (TyForall _ _ t) = getVariables t
> getVariables _ = error "Malformed head of constraint family instance"

constructorName extracts the name of a constructor from a type application term

> constructorName (TyApp (TyCon (UnQual (Ident k))) y) = k
> constructorName (TyApp x y) = constructorName x
> constructorName _ = error "Constraint synonym family instance is malformed"
     
