Author: Dominic Orchard
License: BSD

Prototype implementation of constraint synonsm and constraint families as described in
"Haskell Type Constraints Unleashed" (Dominic Orchard, Tom Schrijvers)

> module Rewrite.Families where
>
> import Data.Either
> import Data.List
> import Data.Maybe

> import Language.Haskell.Exts.Syntax

> import Rewrite.Helpers
> import Rewrite.Unify

> rewriteFamilies (Module srcLoc moduleName opts warning exports imports decls) =
>         Module srcLoc moduleName opts warning exports imports (process decls)

> process ds = correctLineNumbers 0 (processDecls ds 0 emptyEnv)

================================================================================
processDecls : Processes the declarations of a module
================================================================================

> processDecls [] _ _ = []
> processDecls (d:ds) fresh env = 
>    let (ds', fresh', env') = processDecls' d fresh env
>    in  ds'++(processDecls ds fresh' env')

Type Families, if actually being a sneaked in Constraint family, are added to
the family environment

> processDecls' (TypeFamDecl s (Ident name) params kind) fresh env =
>     ([(TypeFamDecl s (Ident name) params kind, 0)], fresh, env')
>     where
>       env' = if ("ConstFam" `isPrefixOf` name) then
>                  addFamily (name, (map varBindToType params)) env
>              else
>                  env

Type Instances, if belonging to a constraint family, are processed to extract
their parameters, and converted into auxilliary GADTs. Their params and corresponding
GADT constructor are added to the environment for later matching instance application.

> processDecls' (TypeInsDecl s t1 t2) fresh env = 
>   let
>     familyName = constructorName t1
>   in
>     if ("ConstFam" `isPrefixOf` familyName) then
>        let
>           consName = Ident $ "ND"++(show fresh)
>           dictName = Ident $ "Dict"++(show fresh)
>           params = getVariables t1
>           gadtParams = map UnkindedVar params
>           instanceParams = flattenTypeApp t1
>           gadtType = tApp (TyCon $ UnQual dictName) (map TyVar params)
>           famInstance = TypeInsDecl s t1 gadtType
>           gadt = GDataDecl s DataType [] dictName gadtParams Nothing [decl] []
>           constraint = interpretTypeAsConstraint t2
>           decl = GadtDecl s consName (TyForall Nothing constraint gadtType)
>           env' = addInstance familyName (instanceParams, "ND"++(show fresh)) env
>        in
>           ([(famInstance, 0), (gadt, 1)], fresh+1, env')
>     else
>        ([((TypeInsDecl s t1 t2),0)], fresh, env)

Class declarations have their inside declarations processed

> processDecls' (ClassDecl s context (Ident name) tv fun classDecls) fresh env =
>     ([(ClassDecl s context (Ident name) tv fun classDecls',0)], fresh', env'')
>       where
>         (classDecls', fresh', env'') = foldl proc ([], fresh, env') classDecls
>         proc (ds, f, t) d = let (ds', f', t') = processClassDecl d f t
>                             in (ds++ds', f', t')
>         env' = addClass (name, (map varBindToType tv)) env

Class instance declarations, have their instance declarations processed, as these
will be modified to include GADT params if constraint family application occurs in
the method contexts.

> processDecls' (InstDecl s c (UnQual (Ident n)) ts decls) fresh env =
>     ([(InstDecl s c (UnQual (Ident n)) ts
>        (map (processInstanceDecl n env ts) decls), 0)], fresh, env)

Type signatures, constraint family applications desugarded into paraams

> processDecls' (TypeSig s names t) fresh env =
>                   ([(TypeSig s names t', 0)], fresh, env')
>                   where
>                     -- if the signature contains constraint family instances,
>                     -- convert to params, and update environment
>                     (t', newParams) = famToParam t env
>                     env' = foldl (\env'' n -> addFun' n newParams env'') env names
     
FunBinds, processed by processMatches

> processDecls' (FunBind matches) fresh env =
>     ([(FunBind (map (processMatches env) matches), 0)], fresh, env)

> processDecls' (PatBind s p t rhs binds) fresh env = 
>     ([(PatBind s p t (processRhs env rhs) (processBinds env binds),0)], fresh, env)

Anything else is left alone

> processDecls' x f t = ([(x, 0)], f, t)

================================================================================
processMatches: goes through function match expressions and calls processExp
                on their bodies
================================================================================

> processMatches env (Match s n p mt rhs binds) = 
>     Match s n p mt (processRhs env rhs) (processBinds env binds)

> processRhs env (UnGuardedRhs exp) = UnGuardedRhs (processExp env exp)
> processRhs env (GuardedRhss guards) = GuardedRhss guards'
>             where guards' = map (\(GuardedRhs s stmts exp) ->
>                    (GuardedRhs s stmts (processExp env exp))) guards  

================================================================================
processExp : processes expression, we expect applications of functions that have 
           constraint family applications in their context to have explicit
           signatures so that we know the correct gadt dummy constructors to use
           -- this is just for our prototype so we don't need type inference

Explicit type signatures must be on variables e.g.
     fmap :: FunctorConst [] a => (a -> b) -> f a -> f b

> processExp env (InfixApp e1 op e2) = InfixApp
>                                     (processExp env e1) op (processExp env e2)
> processExp env (App e1 e2) = App (processExp env e1) (processExp env e2)
> processExp env (NegApp e1) = NegApp (processExp env e1)
> processExp env (Lambda s p e) = Lambda s p (processExp env e)
> processExp env (Let ds e) = Let (processBinds env ds) (processExp env e)
> processExp env (If e1 e2 e3) = If (processExp env e1)
>                                   (processExp env e2)
>                                   (processExp env e3)
> processExp env (Case e alts) = Case (processExp env e) (map (processAlt env) alts)
> processExp env (Tuple exps) = Tuple (map (processExp env) exps)
> processExp env (List exps) = List (map (processExp env) exps)
> processExp env (Paren exp) = Paren (processExp env exp)
> processExp env (LeftSection exp o) = LeftSection (processExp env exp) o
> processExp env (RightSection o exp) = RightSection o (processExp env exp)

> processExp env exp@(ExpTypeSig s (Var (UnQual n)) t) =
>     tApp (Var (UnQual n)) (map ((Con . UnQual . Ident) . (dictConstructor env)) newParams)
>       where (_, newParams) = famToParam t env
         
TODO: process all expressions. generics

> processExp env x = x

> processBinds env (BDecls ds) = BDecls (map fst d')
>                where d' = processDecls ds 0 env
> processBinds env (IPBinds ds) = IPBinds ds'
>                 where ds' = map (\(IPBind s n e) -> (IPBind s n (processExp env e))) ds

> processAlt env (Alt s p guarded binds) =
>                 Alt s p (processGuardedAlt env guarded) (processBinds env binds)

TODO: stmt must also be processed

> processGuardedAlt env (UnGuardedAlt e) = UnGuardedAlt $ processExp env e
> processGuardedAlt env (GuardedAlts gs) = GuardedAlts (map (processGuardedAlts env) gs)
>     where processGuardedAlts env (GuardedAlt s stmt e) = GuardedAlt s stmt (processExp env e)


================================================================================

================================================================================
processClassDecl: deals with class declarations with just the inside declaration

> processClassDecl (ClsDecl d) f e = (d', f', e')
>                          where
>                             d' = map (ClsDecl . fst) d''
>                             (d'', f', e') = processDecls' d f e
>                                    
> processClassDecl x f e = ([x],f,e)

================================================================================
 

================================================================================
Methods for processing class instance declarations

processInstanceDeccl: deals with instance declarations, converting
any instance methods to deal with their gadt paramgs

> processInstanceDecl className env typeParams (InsDecl (FunBind m)) = 
>     (InsDecl (FunBind
>         (map (\m' -> mutateInstanceMethod m' className typeParams env) m)))
> processInstanceDecl _ _ _ x = x


mutateInstanceMethod: changes an instance method to take dummy GADT constructors
       for specific constraint family instances
       renames the old function and generates a new function that wraps it

> mutateInstanceMethod :: Match -> String -> Params -> Env -> Match
> mutateInstanceMethod f@(Match s (Ident n) p t rhs binds)
>                                         className instanceParams env =
>    case findClass className env of
>          -- Belongs to a class we don't know about (yet?)
>       Nothing -> f
>       Just params ->
>           case (findFunctionGadtParams n env) of
>             Nothing -> f
>             Just gadtParams -> 
>               case (mgu params instanceParams) of
>                 Nothing -> f
>                 Just unifier ->
>                   let       
>                    unifiedFunParams = map (\(c, p) -> (c, apply unifier p)) gadtParams
>                    dictConstructors = map (dictConstructor env) unifiedFunParams
>                    oldFun = FunBind [Match s (Ident $ n++"_reserved") p t rhs binds]
>                   in
>                    (Match s (Ident n)
>                      (map (\x -> PApp (UnQual (Ident x)) []) dictConstructors)
>                      Nothing (UnGuardedRhs (Var (UnQual (Ident $ n++"_reserved"))))
>                      (BDecls [oldFun]))

dictConstructor: given a family and some parameters for application
       lookup the corresponding instances for that family in the environment
       then try and unify (using matchesInstance) to get the correct
       GADT constructor

> dictConstructor env (c,p) = 
>     case (findFamInstances c env) of
>       Nothing -> error $ "Family has no instances, therefore can not unify an instance application"
>       Just famInstance -> matchInstance (c, p) famInstance

matchInstance: given an application and a list of instance, try and find an instance
       that matches the application, and return the generated GADT constructor
       corresponding to this instance

> matchInstance (c, p) [] = error $ "No constraint family instances match "++ 
>                            "constraint family application "++(show c)++" "++(show p)
> matchInstance (c, p) ((p', gadtConst):ps) = 
>        case match p p' of
>          Nothing -> matchInstance (c, p) ps
>          -- don't care about the one way unifier, just that unification was successful
>          Just _ -> gadtConst

================================================================================

================================================================================
famToParam: takes a type term. When qualified, converts any constraint family
applications into type parameters

> famToParam (TyForall tyvars context t) env =
>      (TyForall tyvars context' (addParams (map fst params) t), (map snd params))
>           where
>            (context', params) = partitionEithers $ map (famToParam' env) context
> famToParam t _ = (t, [])

famToParam': Does the work of converting a constraint, and removing any class
             families are returning either Left of an unchanged constraint
             or Right of a pair of the type and a params only structure

> famToParam' env a = case a of
>     -- Note can't deal with qualified names, i.e. constraint families
>     -- in another module.
>     c@(ClassA (UnQual (Ident n)) ts) ->
>        if (isFamily ("ConstFam"++n) env) then
>           (Right $ (tApp (TyCon (UnQual (Ident ("ConstFam"++n)))) ts, ("ConstFam"++n, ts)))
>        else
>           (Left $ c)
>     c@(InfixA t1 (UnQual (Ident n)) t2) ->
>        if (isFamily ("ConstFam"++n) env) then
>           (Right $ (TyInfix t1 (UnQual (Ident ("ConstFam"++n))) t2,
>                                                     ("ConstFam"++n, [t1,t2])))
>        else
>           (Left $ c)
>     c -> Left c

================================================================================

================================================================================
Various conversion functions on types/constraints.

                        
addParams: given a type and a list of other parameters, extends the type 
to include these as arguments in a function space

 addParams params t = addParams' (reverse params) t

> addParams [] t = t
> addParams (p:ps) t = TyFun p (addParams ps t)

Instance of the MakeApp are terms, which give their application constructor
which tApp usues to take a constructor term in t and a list of ts, and makes 
a nested, left-asoociative application

> class MakeApp t where
>     tApp :: t -> [t] -> t    
>     tApp con is = tApp' con (reverse is)
>       where
>         tApp' con [] = con
>         tApp' con [i] = cApp con i
>         tApp' cons (i:is) = cApp (tApp' cons is) i


>     cApp :: t -> t -> t

> instance MakeApp Type where
>     cApp = TyApp

> instance MakeApp Exp where
>     cApp = App

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
     
flattenTypeApp takes an application and returnts its parameters in a list

> flattenTypeApp = reverse . flattenTypeApp'
> flattenTypeApp' (TyApp (TyCon (UnQual (Ident k))) y) = [y]
> flattenTypeApp' (TyApp x y) = y:(flattenTypeApp' x)
> flattenTypeApp' x = [x]

varBindToType: converts variable binders to types for unification of 
family declaration parameters with instance declaration parameters

> varBindToType (KindedVar t k) = TyKind (TyVar t) k
> varBindToType (UnkindedVar t) = TyVar t

================================================================================