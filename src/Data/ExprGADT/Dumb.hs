{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}

module Data.ExprGADT.Dumb where

import Data.ExprGADT.Dumb.Types
import Unsafe.Coerce
import Data.ExprGADT.Dumb.Infer
import Data.ExprGADT.Types
import Data.Singletons
import Data.Proxy

data PolyExpr :: * where
    PE :: PolyExpr

data PolyType :: * where
    PT :: Sing n -> (Vec n ETypeW -> ETypeW) -> PolyType

data PNat :: * where
    NZ :: PNat
    NS :: PNat -> PNat

data instance Sing (n :: PNat) where
    SNZ :: Sing 'NZ
    SNS :: Sing (m :: PNat) -> Sing ('NS m)

data Vec :: PNat -> * -> * where
    VNil :: Vec 'NZ a
    (:>) :: a -> Vec n a -> Vec ('NS n) a

infixr 5 :>

type family NPlus (n :: PNat) (m :: PNat) :: PNat where
    NPlus NZ m = m
    NPlus (NS n) m = NS (NPlus n m)

addSN :: forall n m nm. (NPlus n m ~ nm)
      => Sing n -> Sing m -> Sing nm
addSN SNZ y = y
addSN (SNS x) y = SNS (addSN x y)

type family NSub (n :: PNat) (m :: PNat) :: PNat where
    NSub n      NZ      = NZ
    NSub NZ     m       = m
    NSub (NS n) (NS m)  = NSub n m

subSN :: forall n m nm. (NSub n m ~ nm)
      => Sing n -> Sing m -> Sing nm
subSN _ SNZ = SNZ
subSN SNZ y = y
subSN (SNS x) (SNS y) = subSN x y

type family NComp (n :: PNat) (m :: PNat) :: Ordering where
    NComp NZ NZ = EQ
    NComp n NZ = GT
    NComp NZ m = LT
    NComp (NS n) (NS m) = NComp n m

type family NMin (n :: PNat) (m :: PNat) :: PNat where
    NMin n NZ = NZ
    NMin NZ m = NZ
    NMin (NS n) (NS m) = NS (NMin n m)

instance SingI NZ where
    sing = SNZ

instance SingI n => SingI (NS n) where
    sing = SNS sing

takeVec :: Sing n -> Vec m a -> Maybe (Vec n a)
takeVec SNZ _             = Just VNil
takeVec (SNS n) (x :> xs) = (x :>) <$> takeVec n xs
takeVec (SNS _) VNil      = Nothing

applyOnLast :: (Vec m a -> b) -> Sing n -> Vec (NPlus n m) a -> b
applyOnLast f SNZ xs = f xs
applyOnLast f (SNS i) (_ :> xs) = applyOnLast f i xs
applyOnLast _ (SNS _) _ = error "impossible...cannot be called."

collapseTExpr :: TExpr -> PolyType
collapseTExpr (TEV n)  = PT (SNS SNZ) (\(t :> VNil) -> t)    -- todo
collapseTExpr (TEO0 t) = PT SNZ (\_ -> ETW t)
collapseTExpr (TEO1 o t1) = case collapseTExpr t1 of
                              PT n f ->
                                case o of
                                  TOList -> PT n $ \ts ->
                                              case f ts of
                                                ETW t -> ETW (EList t)
collapseTExpr (TEO2 o t1 t2) = case (collapseTExpr t1, collapseTExpr t2) of
                                 (PT (n :: Sing n) f, PT (m :: Sing m) g) ->
                                   PT (addSN n m) $ \(ts :: Vec (NPlus n m) ETypeW) ->
                                     let Just etw1 = f <$> takeVec n ts
                                         etw2 = applyOnLast g n ts
                                     in  case (etw1, etw2) of
                                           (ETW t1', ETW t2') -> case o of
                                                                   TOEither -> ETW (EEither t1' t2')
                                                                   TOTuple -> ETW (ETup t1' t2')
                                                                   TOFunc -> ETW (EFunc t1' t2')
