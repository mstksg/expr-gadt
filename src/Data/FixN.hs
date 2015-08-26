{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}

module Data.FixN where

newtype Fix :: (* -> *) -> * where
    Fix :: { unFix :: f (Fix f) } -> Fix f

newtype Fix2 :: ((k -> *) -> (k -> *)) -> k -> * where
    Fix2 :: { unFix2 :: f (Fix2 f) a } -> Fix2 f a

newtype Fix3 :: ((k -> j -> *) -> (k -> j -> *)) -> k -> j -> * where
    Fix3 :: { unFix3 :: f (Fix3 f) a b } -> Fix3 f a b

