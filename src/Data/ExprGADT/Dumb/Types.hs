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
import Data.Type.Vector

type DBIx = Int

newtype TVar = TV { tvIx :: DBIx }
             deriving (Show, Eq, Ord)

data DumbExpr :: * where
    VD      :: DBIx       -> DumbExpr
    OD      :: Op ts as a -> V (LengthList as) DumbExpr -> DumbExpr
    LambdaD :: DumbExpr   -> DumbExpr

deriving instance Show DumbExpr
