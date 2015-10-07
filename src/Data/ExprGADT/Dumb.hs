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
    NIZ :: NatIxor n
    NIS :: NatIxor n -> NatIxor ('NS n)

-- data Env :: PNat -> * where
--     Env :: Map VName (NatIxor n) -> Vec n ETypeW -> Env n

unDumb :: DumbExpr -> PolyExpr
unDumb e =
    case e of
      DV v -> undefined

