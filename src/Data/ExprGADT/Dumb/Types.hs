{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Data.ExprGADT.Dumb.Types where

import Data.ExprGADT.Types

type VName = String

newtype TVar = TV String
             deriving (Show, Eq, Ord)

data DumbExpr :: * where
    DV      :: VName        -> DumbExpr
    DO0     :: Op0 a        -> DumbExpr
    DO1     :: Op1 a b      -> DumbExpr -> DumbExpr
    DO2     :: Op2 a b c    -> DumbExpr -> DumbExpr -> DumbExpr
    DO3     :: Op3 a b c d  -> DumbExpr -> DumbExpr -> DumbExpr -> DumbExpr
    DLambda :: VName        -> DumbExpr -> DumbExpr

data TExpr :: * where
    TEV      :: TVar    -> TExpr
    TEO0     :: EType a -> TExpr
    TEO1     :: TOp1    -> TExpr -> TExpr
    TEO2     :: TOp2    -> TExpr -> TExpr -> TExpr

data TOp1 :: * where
    TOList :: TOp1
  deriving (Show, Eq)

data TOp2 :: * where
    TOFunc :: TOp2
    TOEither :: TOp2
    TOTuple :: TOp2
  deriving (Show, Eq)

data TypeError :: * where
    TErrUnbound :: VName -> TypeError
    TErrInfType :: TVar -> TExpr -> TypeError
    TErrMismatch :: [TExpr] -> [TExpr] -> TypeError
    TErrUniFail :: TExpr -> TExpr -> TypeError
  deriving Show


deriving instance Show DumbExpr
deriving instance Show TExpr

instance Eq TExpr where
    TEV v  == TEV u  = v == u
    TEO0 t == TEO0 s = eTypeEq t s
    TEO1 o1 t1 == TEO1 o2 t2 = o1 == o2 && t1 == t2
    TEO2 o1 t1 t1' == TEO2 o2 t2 t2' = o1 == o2 && t1 == t2 && t1' == t2'
    _ == _ = False

