{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}

module Data.ExprGADT.Dumb where

-- import Data.ExprGADT.Dumb.Infer
import Control.Applicative
import Control.Exception
import Control.Monad.Except
import Data.ExprGADT.Dumb.Types
import Data.ExprGADT.Eval
import Data.ExprGADT.Traversals
import Data.ExprGADT.Types
import Data.Foldable
import Data.IsTy
import Data.List
import Data.Map.Strict                (Map)
import Data.Maybe
import Data.Monoid
import Data.Proof.EQ                  as Ty
import Data.Proxy
import Data.Singletons
import Data.Singletons.Decide
import Data.Singletons.Prelude hiding (Map)
import Data.Singletons.TH
import Data.Typeable
import Unsafe.Coerce
import qualified Data.Map.Strict      as M

$(singletons [d|

    data PNat = NZ | NS PNat deriving (Eq, Show, Ord)

    nPlus :: PNat -> PNat -> PNat
    nPlus NZ     y = y
    nPlus (NS x) y = NS (nPlus x y)

    nLTE :: PNat -> PNat -> Bool
    nLTE NZ _ = True
    nLTE (NS x) (NS y) = nLTE x y

  |])

data Vec :: PNat -> * -> * where
    VNil :: Vec 'NZ a
    (:>) :: a -> Vec n a -> Vec ('NS n) a

infixr 5 :>

data VecW :: * -> * where
    VW :: Sing n -> Vec n a -> VecW a

type family LengthP (xs :: [k]) :: PNat where
    LengthP '[] = 'NZ
    LengthP (x ': xs) = 'NS (LengthP xs)

takeVec :: Sing n -> Vec m a -> Maybe (Vec n a)
takeVec SNZ _             = Just VNil
takeVec (SNS n) (x :> xs) = (x :>) <$> takeVec n xs
takeVec (SNS _) VNil      = Nothing

applyOnLast :: (Vec m a -> b) -> Sing n -> Vec (NPlus n m) a -> b
applyOnLast f SNZ xs = f xs
applyOnLast f (SNS i) (_ :> xs) = applyOnLast f i xs
applyOnLast _ (SNS _) _ = error "impossible...cannot be called."

data PolyExpr :: * where
    PE :: Sing n -> (Vec n ETypeW -> ExprW) -> PolyExpr

-- data PolyType :: * where
--     PT :: Sing n -> (Vec n ETypeW -> ETypeW) -> PolyType

data TExpr :: PNat -> * where
    TEV      :: NatIxor n -> TExpr n
    TEO0     :: TOp0 -> TExpr n
    TEO1     :: TOp1 -> TExpr n -> TExpr n
    TEO2     :: TOp2 -> TExpr n -> TExpr n -> TExpr n
    TForall  :: TExpr ('NS n) -> TExpr n
  -- deriving (Show, Eq)

data Subst :: PNat -> PNat -> * where
    Sub :: (NatIxor n -> TExpr m) -> Subst n m

data SubstW :: PNat -> * where
    SW :: Sing m -> Subst n m -> SubstW n

unifyTExpr :: forall n m. (SingI n, SingI m)
           => TExpr n
           -> TExpr m
           -> Maybe (SubstW n, SubstW m)
unifyTExpr (TEO0 o) (TEO0 o') | o == o' = Just ( SW (sing :: Sing n) nilSubst
                                               , SW (sing :: Sing m) nilSubst
                                               )
                              | otherwise = Nothing
unifyTExpr (TEO1 o t1) (TEO1 o' t1') | o == o'   = unifyTExpr t1 t1'
                                     | otherwise = Nothing
unifyTExpr (TEO2 o t1 t2) (TEO2 o' t1' t2') | o == o'   = do
                                                (SW ns1 sub1, SW ns1' sub1') <- unifyTExpr t1 t1'
                                                let t1s  = applySubst sub1 t1
                                                    t1s' = applySubst sub1' t1'
                                                (SW ns2 sub2, SW ns2' sub2') <- unifyTExpr t2 t2'
                                                undefined
                                            | otherwise = Nothing
nilSubst :: Subst n n
nilSubst = Sub TEV

subTExpr :: Vec n (TExpr m) -> TExpr n -> TExpr m
subTExpr v = subNix (indexVec v)

applySubst :: Subst n m -> TExpr n -> TExpr m
applySubst (Sub f) = subNix f

subNix :: forall n m. (NatIxor n -> TExpr m) -> TExpr n -> TExpr m
subNix f t = case t of
               TEV ix -> f ix
               TEO0 o -> TEO0 o
               TEO1 o t1 -> TEO1 o (subNix f t1)
               TEO2 o t1 t2 -> TEO2 o (subNix f t1) (subNix f t2)
               TForall t1 -> TForall (subNix f' t1)
  where
    f' :: NatIxor ('NS n) -> TExpr ('NS m)
    f' NIZ = TEV NIZ
    f' (NIS ix) = subNix (TEV . NIS) (f ix)

data ETListW :: * where
    ETLW :: ETList ts -> ETListW

data IndexorW :: [*] -> * where
    IXW :: EType a -> Indexor vs a -> IndexorW vs

deriving instance Show (IndexorW vs)

instance Functor (Vec n) where
    fmap _ VNil = VNil
    fmap f (x :> xs) = f x :> fmap f xs

instance Applicative (Vec 'NZ) where
    pure _ = VNil
    _ <*> _ = VNil

instance Applicative (Vec n) => Applicative (Vec ('NS n)) where
    pure x = x :> pure x
    (f :> fs) <*> (x :> xs) = f x :> (fs <*> xs)

instance Foldable (Vec n) where
    foldMap _ VNil = mempty
    foldMap f (x :> xs) = f x <> foldMap f xs

data NatIxor :: PNat -> * where
    NIZ :: NatIxor ('NS n)
    NIS :: NatIxor n -> NatIxor ('NS n)

indexVec :: Vec n a -> NatIxor n -> a
indexVec (x :> _ ) NIZ      = x
indexVec (_ :> xs) (NIS ix) = indexVec xs ix

-- data Env :: PNat -> * where
--     Env :: Map VName (NatIxor n) -> Vec n ETypeW -> Env n

unDumb :: DumbExpr -> PolyExpr
unDumb e =
    case e of
      DV v -> undefined

