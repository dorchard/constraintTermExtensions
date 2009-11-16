module Main where

constraint MyConstraints a = (Ord a, Show a)

f :: MyConstraints a => a -> a -> String
f x y = if (x<y) then (show x)++" is less than "++(show y)
        else (show x)++" is not less than "++(show y)
