module Main where

import Prelude hiding(Functor, fmap)
import Data.Set

constraint family FunctorConst f a
constraint instance FunctorConst Set a = Ord a
constraint instance FunctorConst [] a = ()

class Functor f where
    fmap :: (FunctorConst f a, FunctorConst f b) => (a -> b) -> f a -> f b

instance Functor Set where
    fmap f = Data.Set.map f

instance Functor [] where
    fmap f = Prelude.map f

x = (fmap :: (FunctorConst [] a , FunctorConst [] b) => (a -> b) -> f a -> f b) (*2) [1,2,3]
y = (fmap :: (FunctorConst Set a , FunctorConst Set b) => (a -> b) -> f a -> f b) (*2) [1,2,3]
