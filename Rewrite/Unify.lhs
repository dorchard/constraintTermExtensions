Author: Dominic Orchard
License: BSD

Prototype implementation of constraint synonsm and constraint families as described in
"Haskell Type Constraints Unleashed" (Dominic Orchard, Tom Schrijvers)

The following code is based on Mark P. Jones "Type Haskell in Haskell" code.

> {-# LANGUAGE FlexibleInstances #-}

> module Rewrite.Unify where

> import Data.List
> import Control.Monad

> import Language.Haskell.Meta
> import Language.Haskell.Exts.Syntax
    
Based on Mark P. Jones' Typing Haskell in Haskell

> type Subst = [(String, Type)]

> nullSubst :: Subst
> nullSubst = []

> (+->) :: String -> Type -> Subst
> u +-> t = [(u, t)]

mgu: (most general unifier) Is used to compute the most general unifying substitution
     between class instances and class declarations.

> class Unify t where
>     mgu :: t -> t -> Maybe Subst

> instance (Term a, Unify a) => Unify [a] where
>     mgu (x:xs) (y:ys) = do s1 <- mgu x y
>                            s2 <- mgu (apply s1 xs) (apply s1 ys)
>                            return (s2 @@ s1)
>     mgu [] [] = return nullSubst
>     mgu _ _ = fail "Unification fail"

> instance (Term a, Unify a) => Unify (a, a) where
>     mgu (t1, t1') (t2, t2') = do s1 <- mgu t1 t1'
>                                  s2 <- mgu (apply s1 t2) (apply s1 t2')
>                                  return (s2 @@ s1)

> instance Unify Type where
>     -- again not sure what to do about varBind!
>    mgu (TyForall varBind context t)
>        (TyForall varBind' context' t') = do 
>                       s1 <- mgu context context'
>                       s2 <- mgu (apply s1 t) (apply s1 t')
>                       return (s2 @@ s1)
>    mgu (TyFun t1 t2) (TyFun t1' t2') = mgu (t1, t1') (t2, t2')
>    mgu (TyTuple _ ts) (TyTuple _ ts') = mgu ts ts'
>    mgu (TyList t) (TyList t') = mgu t t'
>    mgu (TyApp t1 t2) (TyApp t1' t2') = mgu (t1, t1') (t2, t2')
>    mgu (TyVar (Ident v)) t = varBind v t
>    mgu t (TyVar (Ident v)) = varBind v t
>    mgu (TyCon n) (TyCon n') =
>                  if (n==n') then return nullSubst
>                  else fail $ "Constructor mismatch: "++(show n)++" and "++(show n')
>    mgu (TyParen t) (TyParen t') = mgu t t'
>    mgu (TyInfix t1 n t2) (TyInfix t1' n' t2') = 
>                  if (n==n') then mgu (t1, t1') (t2, t2')
>                  else fail $ "Constructor mismatch: "++(show n)++" and "++(show n')
>    mgu (TyKind t k) (TyKind t' k') = 
>                  if (k==k') then mgu t t'
>                  else fail $ "Kind mismatch: "++(show k)++" and "++(show k')
>    mgu _ _ = fail "Failed to unify instance head with class head"

> instance Unify Asst where
>     mgu (ClassA n ts) (ClassA n' ts') = 
>         if (n==n') then return nullSubst
>         else fail $ "Constraint constructor mismathc: "++(show n)++" and "++(show n')
>     mgu (InfixA t1 n t2) (InfixA t1' n' t2') =
>         if (n==n') then mgu (t1, t1') (t2, t2')
>         else fail $ "Constraint constructor mismatch: "++(show n)++" and "++(show n')
>     mgu (IParam n t) (IParam n' t') =
>         if (n==n') then mgu t t'
>         else fail $ "Implicit parameter names mismatch: "++(show n)++" and "++(show n')
>     mgu (EqualP t1 t2) (EqualP t1' t2') = mgu (t1, t1') (t2, t2')
>     mgu _ _ = fail "Failed to unify contexts"
>         


apply: Applies substitutions to a type/constraint

> class Term t where
>     apply :: Subst -> t -> t

     tv :: t -> [TyVar]

> instance Term a => Term [a] where
>     apply s = map (apply s)

> instance Term Type where
>     -- not sure if something must be done with the TyVarBinds
>     apply s (TyForall varBind context t) =
>                            TyForall varBind (apply s context) (apply s t)
>     apply s (TyFun t1 t2) = TyFun (apply s t1) (apply s t2)
>     apply s (TyTuple b ts) = TyTuple b (apply s ts)
>     apply s (TyList t) = TyList (apply s t)
>     apply s (TyApp t1 t2) = TyApp (apply s t1) (apply s t2)
>     apply s (TyVar v) = case v of
>                           Ident a -> case lookup a s of
>                                        Just t -> t
>                                        Nothing -> TyVar (Ident a) 
>                           Symbol a -> case lookup a s of
>                                        Just t -> t
>                                        Nothing -> TyVar (Symbol a)
>     apply s (TyCon q) = TyCon q
>     apply s (TyParen t) = TyParen (apply s t)
>     apply s (TyInfix t1 n t2) = TyInfix (apply s t1) n (apply s t2)
>     apply s (TyKind t k) = TyKind (apply s t) k

> instance Term Asst where
>     apply s (ClassA n ts) = ClassA n (apply s ts)
>     apply s (InfixA t1 n t2) = InfixA (apply s t1) n (apply s t2)
>     apply s (IParam n t) = IParam n (apply s t)
>     apply s (EqualP t1 t2) = EqualP (apply s t1) (apply s t2)

> varBind a t | t == (TyVar (Ident a)) = return nullSubst
>             | otherwise = return (a +-> t)


match is used for matching a constraint family dictionary type to
type instance heads. It is a one way unification, and returns Nothing if it fails

s = match t1 t2 => apply s t1 = t2

> class Matcher t where
>     match :: t -> t -> Maybe Subst

> instance Matcher a => Matcher (a, a) where
>     match (t1, t1') (t2, t2') = do s1 <- match t1 t1'
>                                    s2 <- match t2 t2'
>                                    merge s1 s2

> instance Matcher t => Matcher [t] where
>   match ts ts' = do ss <- sequence (zipWith match ts ts')
>                     foldM merge nullSubst ss

If no match then return Nothing, so that we kno

> instance Matcher Type where
>     -- not considering matching contexts as we will only using matching on
>     --  types
>     match (TyForall varBind context t) (TyForall varBind' context' t') = 
>         match t t'
>     match (TyFun t1 t2) (TyFun t1' t2') = match (t1, t1') (t2, t2')
>     match (TyTuple _ ts) (TyTuple _ ts') = match ts ts'
>     match (TyList t) (TyList t') = match t t'
>     match (TyApp t1 t2) (TyApp t1' t2') = match (t1, t1') (t2, t2')
>     match (TyVar (Ident v)) t = return (v +-> t)
>     match (TyCon c) (TyCon c') = if (c==c') then Just nullSubst
>                                else Nothing
>     match (TyParen t) (TyParen t') = match t t'
>     match (TyInfix t1 n t2) (TyInfix t1' n' t2') = 
>                     if (n==n') then match (t1, t1') (t2, t2')
>                     else Nothing
>     match (TyKind t k) (TyKind t' k') = if (k==k') then match t t'
>                                        else Nothing
>     match _ _ = Nothing
>         

merges two unifiers 

> merge      :: Subst -> Subst -> Maybe Subst
> merge s1 s2 = if agree then return (s1++s2) else fail "merge fails"
>      where agree = all (\v -> apply s1 (TyVar v) == apply s2 (TyVar v))
>                       (map (Ident . fst) s1 `intersect` map (Ident . fst) s2)

(@@): combines two unifiers

> infixr 4 @@
> (@@)       :: Subst -> Subst -> Subst
> s1 @@ s2    = [ (u, apply s1 t) | (u,t) <- s2 ] ++ s1