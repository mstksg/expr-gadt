{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}

module Data.Type.HList where

import Data.Type.Product
import Data.Functor.Identity

type HList = Prod Identity

infixr 5 :<-

pattern (:<-) :: a -> HList as -> HList (a ': as)
pattern x :<- xs = Identity x :< xs
