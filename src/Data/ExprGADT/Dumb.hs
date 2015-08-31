{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Data.ExprGADT.Dumb where

import Data.ExprGADT.Types
import Data.List
import GHC.TypeLits
import Data.Proxy
import Data.Singletons

type Var = Int

data PNat = NZ | NS PNat

data instance Sing (a :: PNat) where
    SNZ :: Sing 'NZ
    SNS :: Sing (a :: PNat) -> Sing ('NS a)

type family CompPN (x :: PNat) (y :: PNat) :: Ordering where
    CompPN 'NZ 'NZ = 'EQ
    CompPN 'NZ ('NS m) = 'LT
    CompPN ('NS n) 'NZ = 'GT
    CompPN ('NS n) ('NS m) = CompPN n m

data PolyExpr :: * where
    PE :: Unfoldable (Vec n) => Sing n -> (Vec n ETypeW -> ExprW) -> PolyExpr

data Vec :: PNat -> * -> * where
    VNil :: Vec 'NZ a
    (:>) :: a -> Vec n a -> Vec ('NS n) a

infixr 5 :>

deriving instance Show e => Show (Vec n e)

class Unfoldable v where
    unfold :: (a -> (b, a)) -> a -> v b

instance Unfoldable (Vec 'NZ) where
    unfold _ _ = VNil

instance Unfoldable (Vec n) => Unfoldable (Vec ('NS n)) where
    unfold f z = let (x, z') = f z
                 in  x :> unfold f z'

replicateU :: Unfoldable v => a -> v a
replicateU = unfold (\y -> (y, y))

fromListV' :: Unfoldable v => a -> [a] -> v a
fromListV' d = unfold $ \xs -> case xs of
                                 [] -> (d, [])
                                 y:ys -> (y, ys)

fromListV :: Unfoldable v => [a] -> v a
fromListV = fromListV' (error "list too short")

indexVec :: (CompPN m n ~ 'GT) => Vec m a -> Sing n -> a
indexVec (x :> _ ) SNZ      = x
indexVec (_ :> xs) (SNS ix) = indexVec xs ix
indexVec _ _                = undefined

data DumbExpr :: * where
    DV      :: Var         -> DumbExpr
    DO0     :: Op0 a       -> DumbExpr
    DO1     :: Op1 a b     -> DumbExpr -> DumbExpr
    DO2     :: Op2 a b c   -> DumbExpr -> DumbExpr -> DumbExpr
    DO3     :: Op3 a b c d -> DumbExpr -> DumbExpr -> DumbExpr -> DumbExpr
    DLambda :: Var         -> DumbExpr -> DumbExpr

deriving instance Show DumbExpr

vToList :: Vec n a -> [a]
vToList VNil = []
vToList (x :> xs) = x : vToList xs

zipLV :: (a -> b -> c) -> [a] -> Vec n b -> Vec n c
zipLV f = zipLV' f (error "list too short")

zipLV' :: (a -> b -> c) -> a -> [a] -> Vec n b -> Vec n c
zipLV' _ _ _ VNil = VNil
zipLV' f d [] (y :> ys) = f d y :> zipLV' f d [] ys
zipLV' f d (x:xs) (y :> ys) = f x y :> zipLV' f d xs ys

testUnDumb :: String
testUnDumb = case unDumb (DV 1) of
               -- PE p f -> show $ f (ETW EInt :> VNil)
               PE _ f -> show $ f (replicateU (ETW EInt))


unDumb :: DumbExpr -> PolyExpr
unDumb e = case e of
             DV v -> PE (SNS SNZ)
                      $ \ts -> case indexVec ts SNZ of
                                 ETW t -> EW (t :* ENil) t (V IZ)
             DO0 o -> case o of
                        I _ -> PE SNZ $ \_ -> EW ENil EInt (O0 o)
                        B _ -> PE SNZ $ \_ -> EW ENil EBool (O0 o)
                        Unit -> PE SNZ $ \_ -> EW ENil EUnit (O0 o)
                        Nil -> PE (SNS SNZ) $ \ts -> case indexVec ts SNZ of
                                                       ETW t -> EW ENil (EList t) (O0 Nil)
