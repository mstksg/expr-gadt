{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}

module Data.ExprGADT.Types where

import Data.Proxy

data Indexor :: [k] -> k -> * where
    IZ :: Indexor (k ': ks) k
    IS :: Indexor ks k -> Indexor (j ': ks) k

data HList :: [*] -> * where
    HNil :: HList '[]
    (:<) :: a -> HList as -> HList (a ': as)

infixr 5 :<

data Expr :: [*] -> * -> * where
    V        :: Indexor vs a     -> Expr vs a
    O0       :: Op0 a            -> Expr vs a
    O1       :: Op1 a b          -> Expr vs a -> Expr vs b
    O2       :: Op2 a b c        -> Expr vs a -> Expr vs b -> Expr vs c
    O3       :: Op3 a b c d      -> Expr vs a -> Expr vs b -> Expr vs c -> Expr vs d
    Lambda   :: Expr (a ': vs) b -> Expr vs (a -> b)

type Maybe' = Either ()

data Op0 :: * -> * where
    I :: Int -> Op0 Int
    B :: Bool -> Op0 Bool
    Nil :: Op0 [a]
    Unit :: Op0 ()

data Op1 :: * -> * -> * where
    Abs    :: Op1 Int Int
    Signum :: Op1 Int Int
    Not    :: Op1 Bool Bool
    Left'  :: Op1 a (Either a b)
    Right' :: Op1 b (Either a b)
    Fst    :: Op1 (a, b) a
    Snd    :: Op1 (a, b) b

data Op2 :: * -> * -> * -> * where
    Plus    :: Op2 Int Int Int
    Times   :: Op2 Int Int Int
    Minus   :: Op2 Int Int Int
    LEquals :: Op2 Int Int Bool
    And     :: Op2 Bool Bool Bool
    Or      :: Op2 Bool Bool Bool
    Tup     :: Op2 a b (a, b)
    Cons    :: Op2 a [a] [a]
    Ap      :: Op2 (a -> b) a b
    Div     :: Op2 Int Int (Maybe' Int)
    Mod     :: Op2 Int Int (Maybe' Int)

data Op3 :: * -> * -> * -> * -> * where
    If       :: Op3 Bool a a a
    Case     :: Op3 (Either a b) (a -> c) (b -> c) c
    UnfoldrN :: Op3 Int (a -> (b, a)) a [b]
    Foldr    :: Op3 (a -> b -> b) b [a] b

data EType :: * -> * where
  EInt :: EType Int
  EBool :: EType Bool
  EUnit :: EType ()
  ETup :: EType a -> EType b -> EType (a, b)
  EEither :: EType a -> EType b -> EType (Either a b)
  EFunc :: EType a -> EType b -> EType (a -> b)
  EList :: EType a -> EType [a]

data ExprW :: * where
    EW :: EType a -> Expr '[] a -> ExprW

data ETypeW :: * where
    ETW :: EType a -> ETypeW

deriving instance Show (Indexor ks k)
deriving instance Show (Op0 a)
deriving instance Show (Op1 a b)
deriving instance Show (Op2 a b c)
deriving instance Show (Op3 a b c d)
deriving instance Show (EType a)
deriving instance Show ExprW
deriving instance Show ETypeW
deriving instance Eq (Indexor ks k)
deriving instance Eq (Op0 a)
deriving instance Eq (Op1 a b)
deriving instance Eq (Op2 a b c)
deriving instance Eq (Op3 a b c d)
-- deriving instance Eq (EType a)
-- deriving instance Eq ExprW

class ToExpr a where
    toExpr :: a -> Expr vs a

instance ToExpr Int where
    toExpr = O0 . I

instance ToExpr Bool where
    toExpr = O0 . B

instance ToExpr () where
    toExpr _ = O0 Unit

instance ToExpr a => ToExpr [a] where
    toExpr []     = O0 Nil
    toExpr (x:xs) = O2 Cons (toExpr x) (toExpr xs)

instance (ToExpr a, ToExpr b) => ToExpr (a, b) where
    toExpr (x, y) = O2 Tup (toExpr x) (toExpr y)

instance (ToExpr a, ToExpr b) => ToExpr (Either a b) where
    toExpr (Left x)  = O1 Left' (toExpr x)
    toExpr (Right x) = O1 Right' (toExpr x)

class MakeEType a where
    makeEType :: p a -> EType a

instance MakeEType () where
    makeEType _ = EUnit

instance MakeEType Int where
    makeEType _ = EInt

instance MakeEType Bool where
    makeEType _ = EBool

instance MakeEType a => MakeEType [a] where
    makeEType _ = EList (makeEType (Proxy :: Proxy a))

instance (MakeEType a, MakeEType b) => MakeEType (a, b) where
    makeEType _ = ETup (makeEType (Proxy :: Proxy a)) (makeEType (Proxy :: Proxy b))

instance (MakeEType a, MakeEType b) => MakeEType (Either a b) where
    makeEType _ = EEither (makeEType (Proxy :: Proxy a)) (makeEType (Proxy :: Proxy b))

instance (MakeEType a, MakeEType b) => MakeEType (a -> b) where
    makeEType _ = EFunc (makeEType (Proxy :: Proxy a)) (makeEType (Proxy :: Proxy b))

instance Num (Expr vs Int) where
    (+)         = O2 Plus
    (*)         = O2 Times
    (-)         = O2 Minus
    abs         = O1 Abs
    signum      = O1 Signum
    fromInteger = O0 . I . fromInteger

exprEq :: Expr vs a -> Expr us b -> Bool
exprEq (V IZ) (V IZ)                           = True
exprEq (V (IS ix1)) (V (IS ix2))               = exprEq (V ix1) (V ix2)
exprEq (O0 o1) (O0 o2)                         = op0Eq o1 o2
exprEq (O1 o1 e1) (O1 o2 e2)                   = op1Eq o1 o2 && exprEq e1 e2
exprEq (O2 o1 e1 e1') (O2 o2 e2 e2')           = op2Eq o1 o2 && exprEq e1 e2 && exprEq e1' e2'
exprEq (O3 o1 e1 e1' e1'') (O3 o2 e2 e2' e2'') = op3Eq o1 o2 && exprEq e1 e2 && exprEq e1' e2' && exprEq e1'' e2''
exprEq (Lambda f1) (Lambda f2)                 = exprEq f1 f2
exprEq _ _                                     = False

op0Eq :: Op0 a -> Op0 b -> Bool
op0Eq (I i1) (I i2) = i1 == i2
op0Eq (B b1) (B b2) = b1 == b2
op0Eq Nil    Nil    = True
op0Eq Unit   Unit   = True
op0Eq _      _      = False

op1Eq :: Op1 a b -> Op1 c d -> Bool
op1Eq Abs Abs       = True
op1Eq Signum Signum = True
op1Eq Not Not       = True
op1Eq Left' Left'   = True
op1Eq Right' Right' = True
op1Eq Fst Fst       = True
op1Eq Snd Snd       = True
op1Eq _   _         = False

op2Eq :: Op2 a b c -> Op2 d e f -> Bool
op2Eq Plus Plus       = True
op2Eq Times Times     = True
op2Eq Minus Minus     = True
op2Eq LEquals LEquals = True
op2Eq And And         = True
op2Eq Or Or           = True
op2Eq Tup Tup         = True
op2Eq Cons Cons       = True
op2Eq Ap Ap           = True
op2Eq Div Div         = True
op2Eq Mod Mod         = True
op2Eq _ _             = False

op3Eq :: Op3 a b c d -> Op3 e f g h -> Bool
op3Eq If If             = True
op3Eq Case Case         = True
op3Eq UnfoldrN UnfoldrN = True
op3Eq Foldr Foldr       = True
op3Eq _ _               = False

instance Eq (Expr vs a) where
    (==) = exprEq

instance Eq (HList '[]) where
    HNil == HNil = True

instance (Eq a, Eq (HList as)) => Eq (HList (a ': as)) where
    x :< xs == y :< ys = x == y && xs == ys

eTypeEq :: EType a -> EType b -> Bool
eTypeEq EInt EInt                     = True
eTypeEq EBool EBool                   = True
eTypeEq EUnit EUnit                   = True
eTypeEq (EList x) (EList y)           = eTypeEq x y
eTypeEq (ETup x y) (ETup x' y')       = eTypeEq x x' && eTypeEq y y'
eTypeEq (EEither x y) (EEither x' y') = eTypeEq x x' && eTypeEq y y'
eTypeEq (EFunc x y) (EFunc x' y')     = eTypeEq x x' && eTypeEq y y'
eTypeEq _ _                           = False

instance Eq (EType a) where
    (==) = eTypeEq

instance Show (Expr vs a) where
    showsPrec p e = showParen (p > 10) $ case e of
                      V ix -> showString "V "
                            . showsPrec 11 ix
                      O0 o -> showString "O0 "
                            . showsPrec 11 o
                      O1 o e1 -> showString "O1 "
                               . showsPrec 11 o
                               . showString " "
                               . showsPrec 11 e1
                      O2 o e1 e2 -> showString "O2 "
                                  . showsPrec 11 o
                                  . showString " "
                                  . showsPrec 11 e1
                                  . showString " "
                                  . showsPrec 11 e2
                      O3 o e1 e2 e3 -> showString "O3 "
                                     . showsPrec 11 o
                                     . showString " "
                                     . showsPrec 11 e1
                                     . showString " "
                                     . showsPrec 11 e2
                                     . showString " "
                                     . showsPrec 11 e3
                      Lambda ef -> showString "Lambda "
                                 . showsPrec 11 ef

instance Show (HList '[]) where
    showsPrec _ HNil = showString "HNil"

instance (Show a, Show (HList as)) => Show (HList (a ': as)) where
    showsPrec p (x :< xs) = showParen (p > 5) $ showsPrec 6 x
                                              . showString " :< "
                                              . showsPrec 5 xs

exprLeafCount :: Expr vs a -> Int
exprLeafCount e = case e of
                    V _ -> 1
                    O0 _ -> 1
                    O1 _ e1 -> exprLeafCount e1
                    O2 _ e1 e2 -> exprLeafCount e1 + exprLeafCount e2
                    O3 _ e1 e2 e3 -> exprLeafCount e1 + exprLeafCount e2 + exprLeafCount e3
                    Lambda ef -> exprLeafCount ef

exprLeafDepths :: Expr vs a -> [Int]
exprLeafDepths e = go 0 e []
  where
    go :: Int -> Expr vs a -> [Int] -> [Int]
    go n e' = case e' of
                V _ -> (n:)
                O0 _ -> (n:)
                O1 _ e1 -> go (n + 1) e1
                O2 _ e1 e2 -> go (n + 1) e1 . go (n + 1) e2
                O3 _ e1 e2 e3 -> go (n + 1) e1 . go (n + 1) e2 . go (n + 1) e3
                Lambda ef -> go (n + 1) ef

infixl 1 ~$
(~$) :: Expr vs (a -> b) -> Expr vs a -> Expr vs b
(~$) = O2 Ap

foldr' :: Expr vs (a -> b -> b) -> Expr vs b -> Expr vs [a] -> Expr vs b
foldr' = O3 Foldr

case' :: Expr vs (Either a b) -> Expr vs (a -> c) -> Expr vs (b -> c) -> Expr vs c
case' = O3 Case

unfoldrN' :: Expr vs Int -> Expr vs (a -> (b, a)) -> Expr vs a -> Expr vs [b]
unfoldrN' = O3 UnfoldrN

if' :: Expr vs Bool -> Expr vs a -> Expr vs a -> Expr vs a
if' = O3 If

right' :: Expr vs b -> Expr vs (Either a b)
right' = O1 Right'

left' :: Expr vs a -> Expr vs (Either a b)
left' = O1 Left'

just' :: Expr vs b -> Expr vs (Maybe' b)
just' = right'

nothing' :: Expr vs (Maybe' b)
nothing' = left' unit'

tup' :: Expr vs a -> Expr vs b -> Expr vs (a, b)
tup' = O2 Tup

fst' :: Expr vs (a, b) -> Expr vs a
fst' = O1 Fst

snd' :: Expr vs (a, b) -> Expr vs b
snd' = O1 Snd

infixr 3 ~&&
(~&&) :: Expr vs Bool -> Expr vs Bool -> Expr vs Bool
(~&&) = O2 And

infixr 2 ~||
(~||) :: Expr vs Bool -> Expr vs Bool -> Expr vs Bool
(~||) = O2 Or

infix 4 ~<=
(~<=) :: Expr vs Int -> Expr vs Int -> Expr vs Bool
(~<=) = O2 LEquals

infix 4 ~==
(~==) :: Expr vs Int -> Expr vs Int -> Expr vs Bool
e1 ~== e2 = (e1 ~<= e2) ~&& (e2 ~<= e1)

infix 4 ~<
(~<) :: Expr vs Int -> Expr vs Int -> Expr vs Bool
e1 ~< e2 = (e1 ~<= e2) ~&& not' (e2 ~<= e1)

infix 4 ~>
(~>) :: Expr vs Int -> Expr vs Int -> Expr vs Bool
e1 ~> e2 = e2 ~< e1

infix 4 ~>=
(~>=) :: Expr vs Int -> Expr vs Int -> Expr vs Bool
e1 ~>= e2 = e2 ~<= e1

not' :: Expr vs Bool -> Expr vs Bool
not' = O1 Not

xor' :: Expr vs Bool -> Expr vs Bool -> Expr vs Bool
xor' e1 e2 = (e1 ~|| e2) ~&& not' (e1 ~&& e2)

infixl 7 `mod'`
mod' :: Expr vs Int -> Expr vs Int -> Expr vs (Maybe' Int)
mod' = O2 Mod

infixl 7 `div'`
div' :: Expr vs Int -> Expr vs Int -> Expr vs (Maybe' Int)
div' = O2 Div

infixr 5 ~:
(~:) :: Expr vs a -> Expr vs [a] -> Expr vs [a]
(~:) = O2 Cons

unit' :: Expr vs ()
unit' = O0 Unit

nil' :: Expr vs [a]
nil' = O0 Nil

false' :: Expr vs Bool
false' = O0 (B False)

true' :: Expr vs Bool
true' = O0 (B True)

iI :: Int -> Expr vs Int
iI = O0 . I

bB :: Bool -> Expr vs Bool
bB = O0 . B

λ :: Expr (a ': vs) b -> Expr vs (a -> b)
λ = Lambda

infixr 0 .->
(.->) :: (Expr (a ': vs) b -> Expr vs (a -> b)) -> Expr (a ': vs) b -> Expr vs (a -> b)
(.->) = ($)

isEEither :: EType a -> Bool
isEEither (EEither _ _) = True
isEEither _ = False

isEFunc :: EType a -> Bool
isEFunc (EFunc _ _) = True
isEFunc _ = False

isCompoundType :: EType a -> Bool
isCompoundType (EEither _ _) = True
isCompoundType (ETup _ _) = True
isCompoundType (EFunc _ _) = True
isCompoundType (EList _) = True
isCompoundType _ = False

eTypeLeaves :: EType a -> Int
eTypeLeaves EInt = 1
eTypeLeaves EBool = 1
eTypeLeaves EUnit = 1
eTypeLeaves (EList x) = eTypeLeaves x
eTypeLeaves (EEither x y) = eTypeLeaves x + eTypeLeaves y
eTypeLeaves (ETup x y) = eTypeLeaves x + eTypeLeaves y
eTypeLeaves (EFunc x y) = eTypeLeaves x + eTypeLeaves y

eTypeNodes :: EType a -> Int
eTypeNodes EInt = 1
eTypeNodes EBool = 1
eTypeNodes EUnit = 1
eTypeNodes (EList x) = 1 + eTypeLeaves x
eTypeNodes (EEither x y) = 1 + eTypeLeaves x + eTypeLeaves y
eTypeNodes (ETup x y) = 1 + eTypeLeaves x + eTypeLeaves y
eTypeNodes (EFunc x y) = 1 + eTypeLeaves x + eTypeLeaves y

eTypeDepth :: EType a -> Int
eTypeDepth EInt = 0
eTypeDepth EBool = 1
eTypeDepth EUnit = 0
eTypeDepth (EList x) = 1 + eTypeDepth x
eTypeDepth (EEither x y) = 1 + max (eTypeDepth x) (eTypeDepth y)
eTypeDepth (ETup x y) = 1 + max (eTypeDepth x) (eTypeDepth y)
eTypeDepth (EFunc x y) = 1 + max (eTypeDepth x) (eTypeDepth y)

absurdIxor :: Indexor '[] a -> b
absurdIxor ix = ix `seq` let x = x in x
