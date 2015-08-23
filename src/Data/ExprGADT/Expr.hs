module Data.ExprGADT.Expr where

import Data.ExprGADT.Types
import Data.ExprGADT.Eval

uncons' :: Expr vs [a] -> Expr vs (Either () (a, [a]))
uncons' = foldr' (λ .-> λ .-> right' (case' (V IZ) caseNil caseCons)) nothing'
  where
    caseNil  = λ .-> tup' (V (IS (IS IZ))) nil'
    caseCons = λ .-> tup' (V (IS (IS IZ))) (fst' (V IZ) ~: snd' (V IZ))

mapMaybe' :: Expr vs (a -> Either () b) -> Expr vs [a] -> Expr vs [b]
mapMaybe' ef = foldr' folder nil'
  where
    folder = λ .-> λ .-> case' (shuffleVars (IS . IS) ef ~$ V (IS IZ))
                               (λ .-> V (IS IZ))
                               (λ .-> V IZ ~: V (IS IZ))

map' :: Expr vs (a -> b) -> Expr vs [a] -> Expr vs [b]
map' ef = mapMaybe' $ λ .-> just' (shuffleVars IS ef ~$ V IZ)

either' :: Expr vs (a -> c) -> Expr vs (b -> c) -> Expr vs (Either a b) -> Expr vs c
either' el er ee = case' ee el er

isRight' :: Expr vs (Either a b) -> Expr vs Bool
isRight' = either' (λ .-> false') (λ .-> true')

filter' :: Expr vs (a -> Bool) -> Expr vs [a] -> Expr vs [a]
filter' ef = mapMaybe' $ λ .-> if' (shuffleVars IS ef ~$ V IZ)
                                   (just' (V IZ))
                                   nothing'

sum' :: Expr vs [Int] -> Expr vs Int
sum' = foldr' (λ .-> λ .-> V IZ + V (IS IZ)) 1

even' :: Expr vs Int -> Expr vs Bool
even' ex = ex `mod'` 2 ~== 0

curry' :: Expr vs ((a, b) -> c) -> Expr vs (a -> b -> c)
curry' ef = λ .-> λ .-> shuffleVars (IS . IS) ef ~$ tup' (V (IS IZ)) (V IZ)

uncurry' :: Expr vs (a -> b -> c) -> Expr vs ((a, b) -> c)
uncurry' ef = λ .-> shuffleVars IS ef ~$ fst' (V IZ) ~$ snd' (V IZ)

