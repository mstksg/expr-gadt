{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}

module Data.ExprGADT.Types where

data Indexor :: [k] -> k -> * where
    IZ :: Indexor (k ': ks) k
    IS :: Indexor ks k -> Indexor (j ': ks) k

data HList :: [*] -> * where
    HNil :: HList '[]
    (:<) :: a -> HList as -> HList (a ': as)

infixr 5 :<

data Expr :: [*] -> * -> * where
    V        :: Indexor vs a                   -> Expr vs a
    O0       :: Op0 a                          -> Expr vs a
    O1       :: O (Op1 a b)     (Op1' a b)     -> Expr vs a             -> Expr vs b
    O2       :: O (Op2 a b c)   (Op2' a b c)   -> Expr vs a             -> Expr vs b        -> Expr vs c
    O3       :: O (Op3 a b c d) (Op3' a b c d) -> Expr vs a             -> Expr vs b        -> Expr vs c   -> Expr vs d
    Lambda   :: Expr (a ': vs) b               -> Expr vs (a -> b)

type Maybe' = Either ()

data O :: * -> * -> * where
    Con :: a -> O a b
    Dec :: b -> O a b
  deriving Show

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

data Op1' :: * -> * -> * where
    Fst    :: Op1' (a, b) a
    Snd    :: Op1' (a, b) b

data Op2 :: * -> * -> * -> * where
    Plus    :: Op2 Int Int Int
    Times   :: Op2 Int Int Int
    Minus   :: Op2 Int Int Int
    Div     :: Op2 Int Int Int
    Mod     :: Op2 Int Int Int
    LEquals :: Op2 Int Int Bool
    And     :: Op2 Bool Bool Bool
    Or      :: Op2 Bool Bool Bool
    Tup     :: Op2 a b (a, b)
    Cons    :: Op2 a [a] [a]

data Op2' :: * -> * -> * -> * where
    Ap       :: Op2' (a -> b) a b

data Op3 :: * -> * -> * -> * -> *

data Op3' :: * -> * -> * -> * -> * where
    If       :: Op3' Bool a a a
    Case     :: Op3' (Either a b) (a -> c) (b -> c) c
    UnfoldrN :: Op3' Int (a -> (b, a)) a [b]
    Foldr    :: Op3' (a -> b -> b) b [a] b

deriving instance Show (Indexor ks k)
deriving instance Show (Op0 a)
deriving instance Show (Op1 a b)
deriving instance Show (Op1' a b)
deriving instance Show (Op2 a b c)
deriving instance Show (Op2' a b c)
deriving instance Show (Op3 a b c d)
deriving instance Show (Op3' a b c d)
deriving instance Eq (Indexor ks k)
deriving instance Eq (Op0 a)
deriving instance Eq (Op1 a b)
deriving instance Eq (Op1' a b)
deriving instance Eq (Op2 a b c)
deriving instance Eq (Op2' a b c)
deriving instance Eq (Op3 a b c d)
deriving instance Eq (Op3' a b c d)

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
    toExpr (x:xs) = O2 (Con Cons) (toExpr x) (toExpr xs)

instance (ToExpr a, ToExpr b) => ToExpr (a, b) where
    toExpr (x, y) = O2 (Con Tup) (toExpr x) (toExpr y)

instance (ToExpr a, ToExpr b) => ToExpr (Either a b) where
    toExpr (Left x)  = O1 (Con Left') (toExpr x)
    toExpr (Right x) = O1 (Con Right') (toExpr x)

onO :: (a -> c) -> (b -> c) -> O a b -> c
onO f _ (Con x) = f x
onO _ g (Dec x) = g x


instance Num (Expr vs Int) where
    (+)         = O2 (Con Plus)
    (*)         = O2 (Con Times)
    (-)         = O2 (Con Minus)
    abs         = O1 (Con Abs)
    signum      = O1 (Con Signum)
    fromInteger = O0 . I . fromInteger

exprEq :: Expr vs a -> Expr us b -> Bool
exprEq (V IZ) (V IZ) = True
exprEq (V (IS ix1)) (V (IS ix2)) = exprEq (V ix1) (V ix2)
exprEq (O0 o1) (O0 o2) = op0Eq o1 o2
exprEq (O1 (Con o1) e1) (O1 (Con o2) e2) = op1Eq o1 o2 && exprEq e1 e2
exprEq (O1 (Dec o1) e1) (O1 (Dec o2) e2) = op1'Eq o1 o2 && exprEq e1 e2
exprEq (O2 (Con o1) e1 e1') (O2 (Con o2) e2 e2') = op2Eq o1 o2 && exprEq e1 e2 && exprEq e1' e2'
exprEq (O2 (Dec o1) e1 e1') (O2 (Dec o2) e2 e2') = op2'Eq o1 o2 && exprEq e1 e2 && exprEq e1' e2'
exprEq (O3 (Con _) e1 e1' e1'') (O3 (Con _) e2 e2' e2'') = exprEq e1 e2 && exprEq e1' e2' && exprEq e1'' e2''
exprEq (O3 (Dec o1) e1 e1' e1'') (O3 (Dec o2) e2 e2' e2'') = op3'Eq o1 o2 && exprEq e1 e2 && exprEq e1' e2' && exprEq e1'' e2''
exprEq (Lambda f1) (Lambda f2) = exprEq f1 f2
exprEq _ _ = False

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
op1Eq _ _           = False

op1'Eq :: Op1' a b -> Op1' c d -> Bool
op1'Eq Fst Fst = True
op1'Eq Snd Snd = True
op1'Eq _   _   = False

op2Eq :: Op2 a b c -> Op2 d e f -> Bool
op2Eq Plus Plus       = True
op2Eq Times Times     = True
op2Eq Minus Minus     = True
op2Eq Div Div         = True
op2Eq Mod Mod         = True
op2Eq LEquals LEquals = True
op2Eq And And         = True
op2Eq Or Or           = True
op2Eq Tup Tup         = True
op2Eq Cons Cons       = True
op2Eq _ _             = False

op2'Eq :: Op2' a b c -> Op2' d e f -> Bool
op2'Eq Ap Ap = True

op3'Eq :: Op3' a b c d -> Op3' e f g h -> Bool
op3'Eq If If             = True
op3'Eq Case Case         = True
op3'Eq UnfoldrN UnfoldrN = True
op3'Eq Foldr Foldr       = True
op3'Eq _ _               = False

instance Eq (Expr vs a) where
    (==) = exprEq

instance Eq (HList '[]) where
    HNil == HNil = True

instance (Eq a, Eq (HList as)) => Eq (HList (a ': as)) where
    x :< xs == y :< ys = x == y && xs == ys

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

infixl 1 ~$
(~$) :: Expr vs (a -> b) -> Expr vs a -> Expr vs b
(~$) = O2 (Dec Ap)

foldr' :: Expr vs (a -> b -> b) -> Expr vs b -> Expr vs [a] -> Expr vs b
foldr' = O3 (Dec Foldr)

case' :: Expr vs (Either a b) -> Expr vs (a -> c) -> Expr vs (b -> c) -> Expr vs c
case' = O3 (Dec Case)

unfoldrN' :: Expr vs Int -> Expr vs (a -> (b, a)) -> Expr vs a -> Expr vs [b]
unfoldrN' = O3 (Dec UnfoldrN)

if' :: Expr vs Bool -> Expr vs a -> Expr vs a -> Expr vs a
if' = O3 (Dec If)

right' :: Expr vs b -> Expr vs (Either a b)
right' = O1 (Con Right')

left' :: Expr vs a -> Expr vs (Either a b)
left' = O1 (Con Left')

just' :: Expr vs b -> Expr vs (Maybe' b)
just' = right'

nothing' :: Expr vs (Maybe' b)
nothing' = left' unit'

tup' :: Expr vs a -> Expr vs b -> Expr vs (a, b)
tup' = O2 (Con Tup)

fst' :: Expr vs (a, b) -> Expr vs a
fst' = O1 (Dec Fst)

snd' :: Expr vs (a, b) -> Expr vs b
snd' = O1 (Dec Snd)

infixr 3 ~&&
(~&&) :: Expr vs Bool -> Expr vs Bool -> Expr vs Bool
(~&&) = O2 (Con And)

infixr 2 ~||
(~||) :: Expr vs Bool -> Expr vs Bool -> Expr vs Bool
(~||) = O2 (Con Or)

infix 4 ~<=
(~<=) :: Expr vs Int -> Expr vs Int -> Expr vs Bool
(~<=) = O2 (Con LEquals)

infix 4 ~==
(~==) :: Expr vs Int -> Expr vs Int -> Expr vs Bool
e1 ~== e2 = (e1 ~<= e2) ~&& (e2 ~<= e1)

infixl 7 `mod'`
mod' :: Expr vs Int -> Expr vs Int -> Expr vs Int
mod' = O2 (Con Mod)

infixl 7 `div'`
div' :: Expr vs Int -> Expr vs Int -> Expr vs Int
div' = O2 (Con Div)

infixr 5 ~:
(~:) :: Expr vs a -> Expr vs [a] -> Expr vs [a]
(~:) = O2 (Con Cons)

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
-- (.->) :: (Expr (a ': vs) b -> Expr vs (a -> b)) -> Expr (a ': vs) b -> Expr vs (a -> b)
-- (.->) :: (a -> b) -> a -> b
(.->) = ($)

