{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}

module Data.ExprGADT.Samples where

import Data.ExprGADT.Types
import Data.Type.Combinator hiding (I)
import Data.Type.Product

testNilP :: ExprP vs (EType a -> [a])
testNilP = LambdaP (TP TOStar Ø) (OP Nil (only (Comp $ VP i1)) Ø)

testIdP :: ExprP vs (EType a -> a -> a)
testIdP = LambdaP (TP TOStar Ø) (LambdaP (VP i1) (VP i1))

testConstP :: ExprP vs (EType a -> EType b -> a -> b -> a)
testConstP = LambdaP (TP TOStar Ø)
           $ LambdaP (TP TOStar Ø)
           $ LambdaP (VP i2)
           $ LambdaP (VP i2)
           $ VP i2

testCompP :: ExprP vs (EType a -> EType b -> EType c -> (b -> c) -> (a -> b) -> a -> c)
testCompP = LambdaP (TP TOStar Ø)
          $ LambdaP (TP TOStar Ø)
          $ LambdaP (TP TOStar Ø)
          $ LambdaP (TP TOFunc (Comp (VP i2) :> Comp (VP i1)))
          $ LambdaP (TP TOFunc (Comp (VP i4) :> Comp (VP i3)))
          $ LambdaP (VP i5)
          $ O2p Ap (Comp (VP i5) :> Comp (VP i4)) (VP i3)
          $ O2p Ap (Comp (VP i6) :> Comp (VP i5)) (VP i2) (VP i1)

testFacP :: forall vs. ExprP vs (Int -> Int)
testFacP = LambdaP (TP TOInt Ø)
        $ O3p Foldr (Comp (TP TOInt Ø) :> Comp (TP TOInt Ø)) times (O0p (I 1) Ø) xs
  where
    times :: ExprP (Int ': vs) (Int -> Int -> Int)
    times = LambdaP (TP TOInt Ø)
          $ LambdaP (TP TOInt Ø)
          $ O2p Times Ø (VP IZ) (VP (IS IZ))
    xs :: ExprP (Int ': vs) [Int]
    xs = O3p UnfoldrN
               (Comp (TP TOInt Ø) :> Comp (TP TOInt Ø))
               (O2p Minus Ø (VP IZ) (O0p (I 1) Ø))
               f
               (O0p (I 1) Ø)
    f :: ExprP (Int ': vs) (Int -> (Int, Int))
    f = LambdaP (TP TOInt Ø)
      $ O2p Tup (Comp (TP TOInt Ø) :> Comp (TP TOInt Ø)) izsuc izsuc
      where
        izsuc :: ExprP (Int ': Int ': vs) Int
        izsuc = O2p Plus Ø (VP IZ) (O0p (I 1) Ø)

testReplicate :: forall vs a. ExprP vs (EType a -> Int -> a -> [a])
testReplicate = LambdaP (TP TOStar Ø)
              $ LambdaP (TP TOInt Ø)
              $ LambdaP (VP i2)
              $ O3p UnfoldrN
                      (Comp (TP TOUnit Ø) :> Comp (VP i3))
                      (VP i2)
                      (LambdaP (TP TOUnit Ø) (O2p Tup
                                                    (Comp (VP i4) :> Comp (TP TOUnit Ø))
                                                    (VP i2)
                                                    (VP i1)
                                             ))
                      (O0p Unit Ø)

testComp :: Expr vs ((b -> c) -> (a -> b) -> a -> c)
testComp = Lambda
         $ Lambda
         $ Lambda
         $ O2 Ap (V (IS (IS IZ))) (O2 Ap (V (IS IZ)) (V IZ))

