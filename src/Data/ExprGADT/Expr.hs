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

module Data.ExprGADT.Expr where

import Data.List (unfoldr)

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

forbidden :: Expr vs a -> String -> b
forbidden e r = error $ "Impossible branch prevented by type system! " ++ show e ++ " " ++ r

eval :: Expr '[] a -> a
eval = evalWith HNil

evalWith :: forall vs a. HList vs -> Expr vs a -> a
evalWith vs = go
  where
    go :: forall b. Expr vs b -> b
    go e = case reduceAll e of
             V ix                -> subIndexor vs ix
             O0 o                -> op0 o
             O1 o e1             -> onO op1 op1' o (go e1)
             O2 o e1 e2          -> onO op2 op2' o (go e1) (go e2)
             O3 o e1 e2 e3       -> onO op3 op3' o (go e1) (go e2) (go e3)
             Lambda ef           -> \x -> evalWith (x :< vs) ef

onO :: (a -> c) -> (b -> c) -> O a b -> c
onO f _ (Con x) = f x
onO _ g (Dec x) = g x

subIndexor :: forall ks. HList ks -> (forall v. Indexor ks v -> v)
subIndexor (x :< _ ) IZ      = x
subIndexor (_ :< xs) (IS ix) = subIndexor xs ix
subIndexor HNil      _       = error "Impossible...should be prevented by the type system. There is no Indexor '[] a."


reduceAll :: Expr vs a -> Expr vs a
reduceAll e | e == e'   = e'
            | otherwise = reduceAll e'
  where
    e' = reduceWith V e

reduce :: Expr vs a -> Expr vs a
reduce = reduceWith V

reduceWith :: forall vs us o. (forall v. Indexor vs v -> Expr us v) -> Expr vs o -> Expr us o
reduceWith f = go
  where
    go :: Expr vs a -> Expr us a
    go e = case e of
             V ix              -> f ix
             O0 o              -> O0 o
             O1 o e1           -> case o of
                                    Con o'     -> case e1 of
                                                    O0 o'' -> case op1_ o' (op0 o'') of
                                                                Just x -> O0 x
                                                                _      -> O1 o (go e1)
                                                    _      -> O1 o (go e1)
                                    Dec Fst    -> reduceFst e1
                                    Dec Snd    -> reduceSnd e1
             O2 o e1 e2        -> case o of
                                    Con o' -> case (e1, e2) of
                                                (O0 o''1, O0 o''2) -> case op2_ o' (op0 o''1) (op0 o''2) of
                                                                        Just x -> O0 x
                                                                        _      -> O2 o (go e1) (go e2)
                                                _           -> O2 o (go e1) (go e2)
                                    Dec Ap -> reduceAp e1 e2
             O3 o e1 e2 e3     -> case o of
                                    Con _        -> forbidden e "There aren't even any constructors for Op3.  How absurd."
                                    Dec If       -> reduceIf e1 e2 e3
                                    Dec Case     -> reduceCase e1 e2 e3
                                    Dec UnfoldrN -> reduceUnfoldrN e1 e2 e3
                                    Dec Foldr    -> reduceFoldr e1 e2 e3
             Lambda eλ         -> Lambda (go' eλ)
    reduceFst :: Expr vs (a, b) -> Expr us a
    reduceFst e' = case e' of
                     O2 (Con Tup) e1 _ -> go e1
                     _                 -> O1 (Dec Fst) (go e')
    reduceSnd :: Expr vs (a, b) -> Expr us b
    reduceSnd e' = case e' of
                     O2 (Con Tup) _ e2 -> go e2
                     _                 -> O1 (Dec Snd) (go e')
    reduceIf :: Expr vs Bool -> Expr vs a -> Expr vs a -> Expr us a
    reduceIf eb ex ey = case eb of
                          O0 (B b) | b         -> go ex
                                   | otherwise -> go ey
                          _                    -> O3 (Dec If) (go eb) (go ex) (go ey)
    reduceAp :: forall a b. Expr vs (a -> b) -> Expr vs a -> Expr us b
    reduceAp ef ex = case ef of
                       Lambda eλ -> go $ reduceWith apply eλ
                       _         -> O2 (Dec Ap) (go ef) (go ex)
      where
        apply :: forall k. Indexor (a ': vs) k -> Expr vs k
        apply IZ      = ex
        apply (IS ix) = V ix
    reduceCase :: forall a b c. Expr vs (Either a b) -> Expr vs (a -> c) -> Expr vs (b -> c) -> Expr us c
    reduceCase ee el er = case ee of
                            O1 (Con Left') ex  -> reduceAp el ex
                            O1 (Con Right') ex -> reduceAp er ex
                            _                  -> O3 (Dec Case) (go ee) (go el) (go er)
    reduceUnfoldrN :: Expr vs Int -> Expr vs (a -> (b, a)) -> Expr vs a -> Expr us [b]
    reduceUnfoldrN en ef ez = case reduce en of
                                O0 (I i) | i <= 0    -> O0 Nil
                                         | otherwise -> go (unfold i)
                                _                    -> O3 (Dec UnfoldrN) (go en) (go ef) (go ez)
      where
        unfold i = O2 (Dec Ap) (Lambda (O2 (Con Cons) (O1 (Dec Fst) (V IZ))
                                                      (O3 (Dec UnfoldrN) (O0 (I (i - i)))
                                                                         (shuffleVars IS ef)
                                                                         (O1 (Dec Snd) (V IZ))
                                                      )
                                       )
                               )
                               (O2 (Dec Ap) ef ez)
    reduceFoldr :: Expr vs (a -> b -> b) -> Expr vs b -> Expr vs [a] -> Expr us b
    reduceFoldr ef ez exs = case reduce exs of
                              O0 Nil               -> go ez
                              O2 (Con Cons) ey eys -> go $ ef ~$ ey
                                                              ~$ O3 (Dec Foldr) ef ez eys
                              _                    -> O3 (Dec Foldr) (go ef) (go ez) (go exs)
    go' :: forall d a. Expr (d ': vs) a -> Expr (d ': us) a
    go' = reduceWith f'
      where
        f' :: forall k. Indexor (d ': vs) k  -> Expr (d ': us) k
        f' IZ      = V IZ
        f' (IS ix) = shuffleVars IS $ f ix

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

just' :: Expr vs b -> Expr vs (Either () b)
just' = right'

nothing' :: Expr vs (Either () b)
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

λ :: Expr (a ': vs) b -> Expr vs (a -> b)
λ = Lambda

infixr 0 .->
(.->) :: (Expr (a ': vs) b -> Expr vs (a -> b)) -> Expr (a ': vs) b -> Expr vs (a -> b)
(.->) = ($)

uncons' :: Expr vs [a] -> Expr vs (Either () (a, [a]))
uncons' = foldr' (λ .-> λ .-> right' (case' (V IZ) caseNil caseCons)) nothing'
  where
    caseNil  = λ .-> tup' (V (IS (IS IZ))) nil'
    caseCons = λ .-> tup' (V (IS (IS IZ))) (fst' (V IZ) ~: snd' (V IZ))

mapMaybe' :: Expr vs (a -> Either () b) -> Expr vs [a] -> Expr vs [b]
mapMaybe' ef = foldr' folder nil'
  where
    folder = λ .-> λ .-> case' (shuffleVars (IS . IS) ef ~$ V (IS IZ))
                               (λ .-> V (IS IZ))
                               (λ .-> V IZ ~: V (IS IZ))

map' :: Expr vs (a -> b) -> Expr vs [a] -> Expr vs [b]
map' ef = mapMaybe' $ λ .-> just' (shuffleVars IS ef ~$ V IZ)

either' :: Expr vs (a -> c) -> Expr vs (b -> c) -> Expr vs (Either a b) -> Expr vs c
either' el er ee = case' ee el er

isRight' :: Expr vs (Either a b) -> Expr vs Bool
isRight' = either' (λ .-> false') (λ .-> true')

filter' :: Expr vs (a -> Bool) -> Expr vs [a] -> Expr vs [a]
filter' ef = mapMaybe' $ λ .-> if' (shuffleVars IS ef ~$ V IZ)
                                   (just' (V IZ))
                                   nothing'

sum' :: Expr vs [Int] -> Expr vs Int
sum' = foldr' (λ .-> λ .-> V IZ + V (IS IZ)) 1

even' :: Expr vs Int -> Expr vs Bool
even' ex = ex `mod'` 2 ~== 0

curry' :: Expr vs ((a, b) -> c) -> Expr vs (a -> b -> c)
curry' ef = λ .-> λ .-> shuffleVars (IS . IS) ef ~$ tup' (V (IS IZ)) (V IZ)

uncurry' :: Expr vs (a -> b -> c) -> Expr vs ((a, b) -> c)
uncurry' ef = λ .-> shuffleVars IS ef ~$ fst' (V IZ) ~$ snd' (V IZ)

shuffleVars :: forall ks js c. (forall k. Indexor ks k -> Indexor js k) -> Expr ks c -> Expr js c
shuffleVars f = reduceWith (V . f)

pushDown :: (Indexor ks k -> Indexor js k) -> Indexor (a ': ks) k -> Indexor (a ': js) k
pushDown f ix = case ix of
                  IZ     -> IZ
                  IS ix' -> IS (f ix')

op0 :: Op0 a -> a
op0 (I i) = i
op0 (B b) = b
op0 Nil   = []
op0 Unit  = ()

op1 :: Op1 a b -> a -> b
op1 Abs    = abs
op1 Signum = signum
op1 Not    = not
op1 Left'  = Left
op1 Right' = Right

op1_ :: Op1 a b -> a -> Maybe (Op0 b)
op1_ o = modder . op1 o
  where
    modder = case o of
               Abs    -> Just . I
               Signum -> Just . I
               Not    -> Just . B
               Left'  -> const Nothing
               Right' -> const Nothing

op1' :: Op1' a b -> a -> b
op1' Fst = fst
op1' Snd = snd

op2 :: Op2 a b c -> a -> b -> c
op2 Plus    = (+)
op2 Times   = (*)
op2 Minus   = (-)
op2 Div     = div
op2 Mod     = mod
op2 LEquals = (<=)
op2 And     = (&&)
op2 Or      = (||)
op2 Tup     = (,)
op2 Cons    = (:)

op2_ :: Op2 a b c -> a -> b -> Maybe (Op0 c)
op2_ o x y = modder (op2 o x y)
  where
    modder = case o of
               Plus    -> Just . I
               Times   -> Just . I
               Minus   -> Just . I
               Div     -> Just . I
               Mod     -> Just . I
               LEquals -> Just . B
               And     -> Just . B
               Or      -> Just . B
               Tup     -> const Nothing
               Cons    -> const Nothing

op2' :: Op2' a b c -> a -> b -> c
op2' Ap = ($)

op3 :: Op3 a b c d -> a -> b -> c -> d
op3 = error "No constructors of Op3.  How absurd!"

op3' :: Op3' a b c d -> a -> b -> c -> d
op3' If       = \b x y -> if b then x else y
op3' Case     = \e l r -> either l r e
op3' UnfoldrN = \n f z -> take n $ unfoldr (Just . f) z
op3' Foldr    = foldr


instance Num (Expr vs Int) where
    (+)         = O2 (Con Plus)
    (*)         = O2 (Con Times)
    (-)         = O2 (Con Minus)
    abs         = O1 (Con Abs)
    signum      = O1 (Con Signum)
    fromInteger = O0 . I . fromInteger

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

lengthHList :: HList vs -> Int
lengthHList HNil = 0
lengthHList (_ :< xs) = 1 + lengthHList xs
