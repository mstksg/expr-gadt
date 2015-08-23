{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

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
    folder = λ .-> λ .-> case' (pushInto ef ~$ V (IS IZ))
                               (λ .-> V (IS IZ))
                               (λ .-> V IZ ~: V (IS IZ))

map' :: Expr vs (a -> b) -> Expr vs [a] -> Expr vs [b]
map' ef = mapMaybe' $ λ .-> just' (pushInto ef ~$ V IZ)

either' :: Expr vs (a -> c) -> Expr vs (b -> c) -> Expr vs (Either a b) -> Expr vs c
either' el er ee = case' ee el er

isRight' :: Expr vs (Either a b) -> Expr vs Bool
isRight' = either' (λ .-> false') (λ .-> true')

filter' :: Expr vs (a -> Bool) -> Expr vs [a] -> Expr vs [a]
filter' ef = mapMaybe' $ λ .-> if' (pushInto ef ~$ V IZ)
                                   (just' (V IZ))
                                   nothing'

sum' :: Expr vs [Int] -> Expr vs Int
sum' = foldr' (λ .-> λ .-> V IZ + V (IS IZ)) 0

even' :: Expr vs Int -> Expr vs Bool
even' ex = ex `mod'` 2 ~== 0

curry' :: Expr vs ((a, b) -> c) -> Expr vs (a -> b -> c)
curry' ef = λ .-> λ .-> pushInto ef ~$ tup' (V (IS IZ)) (V IZ)

uncurry' :: Expr vs (a -> b -> c) -> Expr vs ((a, b) -> c)
uncurry' ef = λ .-> pushInto ef ~$ fst' (V IZ) ~$ snd' (V IZ)

enumFromTo' :: Expr vs Int -> Expr vs Int -> Expr vs [Int]
enumFromTo' e1 e2 = unfoldrN' (e2 - e1 + 1) (λ .-> tup' (V IZ) (V IZ + 1)) e1

-- can be more general:
-- inLambda :: (Expr (a' ': vs) a' -> Expr (a ': us) b) -> Expr us (a -> b)
inLambda :: (Expr (a ': vs) a -> Expr (a ': vs) b) -> Expr vs (a -> b)
inLambda f = λ .-> f (V IZ)

inLambda2 :: (Expr (b ': a ': vs) a -> Expr (b ': a ': vs) b -> Expr (b ': a ': vs) c)
          -> Expr vs (a -> b -> c)
inLambda2 f = λ .-> λ .-> f (V (IS IZ)) (V IZ)

inLambda3 :: (Expr (c ': b ': a ': vs) a -> Expr (c ': b ': a ': vs) b -> Expr (c ': b ': a ': vs) c -> Expr (c ': b ': a ': vs) d)
          -> Expr vs (a -> b -> c -> d)
inLambda3 f = λ .-> λ .-> λ .-> f (V (IS (IS IZ))) (V (IS IZ)) (V IZ)
