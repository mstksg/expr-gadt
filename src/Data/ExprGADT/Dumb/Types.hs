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

newtype TVar = TV { tvVName :: VName }
             deriving (Show, Eq, Ord)

data DumbExpr :: * where
    DV      :: VName        -> DumbExpr
    DO0     :: Op0 a        -> DumbExpr
    DO1     :: Op1 a b      -> DumbExpr -> DumbExpr
    DO2     :: Op2 a b c    -> DumbExpr -> DumbExpr -> DumbExpr
    DO3     :: Op3 a b c d  -> DumbExpr -> DumbExpr -> DumbExpr -> DumbExpr
    DLambda :: VName        -> DumbExpr -> DumbExpr

data TOp0 :: * where
    TOInt ::  TOp0
    TOBool ::  TOp0
    TOUnit ::  TOp0
  deriving (Show, Eq)

data TOp1 :: * where
    TOList :: TOp1
  deriving (Show, Eq)

data TOp2 :: * where
    TOFunc :: TOp2
    TOEither :: TOp2
    TOTuple :: TOp2
  deriving (Show, Eq)

deriving instance Show DumbExpr
