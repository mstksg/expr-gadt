{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Data.ExprGADT.Types where

-- import Control.Applicative
-- import Data.IsTy
-- import Data.Monoid
-- import Data.Proof.EQ
import Data.Proxy
-- import Data.Type.Combinator
import Data.Type.Product
import Type.Family.List        as L

data Indexor :: [k] -> k -> * where
    IZ :: Indexor (k ': ks) k
    IS :: Indexor ks k -> Indexor (j ': ks) k

type ETList = Prod EType
type ExprList vs = Prod (Expr vs)

type ExprPList vs = Prod (ExprP vs)
type ExprPET vs a = ExprP vs (EType a)
type ExprPETList vs ts = Prod (ExprP vs) (EType L.<$> ts)

-- type family ExprET vs a where
--     ExprET vs a = Expr vs (EType a)

-- data HList :: [*] -> * where
--     HNil :: HList '[]
--     (:<) :: a -> HList as -> HList (a ': as)

-- infixr 5 :<

-- data ExList :: [*] -> [*] -> * where
--     ExNil :: ExList vs '[]
--     (:%)  :: Expr vs t -> ExList vs ts -> ExList vs (a ': ts)

-- data ETExList :: [*] -> [*] -> * where
--     ETExNil :: ETExList vs '[]
--     (:$)    :: Expr vs (EType t) -> ExprList vs ts -> ExprList vs (a ': ts)

-- type family ListOf :: (* -> *) -> [*] -> * where
--     ListOf f []


data Expr :: [*] -> * -> * where
    V        :: Indexor vs a     -> Expr vs a
    O        :: Op ts as a       -> ExprList vs as -> Expr vs a
    Lambda   :: Expr (a ': vs) b -> Expr vs (a -> b)

data ExprP :: [*] -> * -> * where
    VP       :: Indexor vs a -> ExprP vs a
    TP       :: EType a -> ExprP vs (EType a)
    -- StarP    :: ExprP vs (EType (EType a))
    OP       :: Op ts as a -> ExprPETList vs ts -> ExprPList vs as -> ExprP vs a
    LambdaP  :: ExprP vs (EType a) -> ExprP (a ': vs) b -> ExprP vs (a -> b)

testNil :: ExprP vs (EType a -> [a])
testNil = LambdaP (TP EStar) (OP Nil (only (VP IZ)) Ø)

testId :: ExprP vs (EType a -> a -> a)
testId = LambdaP (TP EStar) (LambdaP (VP IZ) (VP IZ))

testConst :: ExprP vs (EType a -> EType b -> a -> b -> a)
testConst = LambdaP (TP EStar)
          $ LambdaP (TP EStar)
          $ LambdaP (VP (IS IZ))
          $ LambdaP (VP (IS IZ))
          $ VP (IS IZ)

type Maybe' = Either ()

data Op :: [*] -> [*] -> * -> * where
    I        :: Int  -> Op '[]  '[] Int
    B        :: Bool -> Op '[]  '[] Bool
    Unit     ::         Op '[]  '[] ()
    Nil      ::         Op '[a] '[] [a]

    Abs      :: Op '[]     '[Int   ] Int
    Signum   :: Op '[]     '[Int   ] Int
    Not      :: Op '[]     '[Bool  ] Bool
    Left'    :: Op '[a, b] '[a     ] (Either a b)
    Right'   :: Op '[a, b] '[b     ] (Either a b)
    Fst      :: Op '[a, b] '[(a, b)] a
    Snd      :: Op '[a, b] '[(a, b)] b

    Plus     :: Op '[]     '[Int   , Int ] Int
    Times    :: Op '[]     '[Int   , Int ] Int
    Minus    :: Op '[]     '[Int   , Int ] Int
    LEquals  :: Op '[]     '[Int   , Int ] Bool
    And      :: Op '[]     '[Bool  , Bool] Bool
    Or       :: Op '[]     '[Bool  , Bool] Bool
    Tup      :: Op '[a, b] '[a     , b   ] (a, b)
    Cons     :: Op '[a]    '[a     , [a] ] [a]
    Ap       :: Op '[a, b] '[a -> b, a   ] b
    Div      :: Op '[]     '[Int   , Int ] (Maybe' Int)
    Mod      :: Op '[]     '[Int   , Int ] (Maybe' Int)

    If       :: Op '[a]       '[Bool       , a          , a     ] a
    Case     :: Op '[a, b, c] '[Either a b , a -> c     , b -> c] c
    UnfoldrN :: Op '[a, b]    '[Int        , a -> (b, a), a     ] [b]
    Foldr    :: Op '[a, b]    '[a -> b -> b, b          , [a]   ] b

type Op0 ts = Op ts '[]
type Op1 ts a = Op ts '[a]
type Op2 ts a b = Op ts '[a, b]
type Op3 ts a b c = Op ts '[a, b, c]

data EType :: * -> * where
  EInt    :: EType Int
  EBool   :: EType Bool
  EUnit   :: EType ()
  EEither :: EType a -> EType b -> EType (Either a b)
  ETup    :: EType a -> EType b -> EType (a, b)
  EFunc   :: EType a -> EType b -> EType (a -> b)
  EList   :: EType a -> EType [a]
  -- ???? is this a bad ideaaaa
  EStar   :: EType (EType a)

class HasEType a where
    eType :: p a -> EType a

instance HasEType () where
    eType _ = EUnit

instance HasEType Int where
    eType _ = EInt

instance HasEType Bool where
    eType _ = EBool

instance HasEType a => HasEType [a] where
    eType _ = EList (eType (Proxy :: Proxy a))

instance (HasEType a, HasEType b) => HasEType (a, b) where
    eType _ = ETup (eType (Proxy :: Proxy a)) (eType (Proxy :: Proxy b))

instance (HasEType a, HasEType b) => HasEType (Either a b) where
    eType _ = EEither (eType (Proxy :: Proxy a)) (eType (Proxy :: Proxy b))

instance (HasEType a, HasEType b) => HasEType (a -> b) where
    eType _ = EFunc (eType (Proxy :: Proxy a)) (eType (Proxy :: Proxy b))

class HasEType a => ToExpr a where
    toExpr  :: a -> Expr vs a
    toExprP :: a -> ExprP vs a

instance ToExpr Int where
    toExpr = o0 . I
    toExprP i = OP (I i) Ø Ø

instance ToExpr Bool where
    toExpr = o0 . B
    toExprP b = OP (B b) Ø Ø

instance ToExpr () where
    toExpr _ = o0 Unit
    toExprP _ = OP Unit Ø Ø

instance ToExpr a => ToExpr [a] where
    toExpr []     = o0 Nil
    toExpr (x:xs) = o2 Cons (toExpr x) (toExpr xs)
    toExprP xs = case xs of
                   []   -> OP Nil t Ø
                   y:ys -> OP Cons t (toExprP y :< toExprP ys :< Ø)
      where
        t = only . TP $ eType (Proxy :: Proxy a)

instance (ToExpr a, ToExpr b) => ToExpr (a, b) where
    toExpr (x, y) = o2 Tup (toExpr x) (toExpr y)
    toExprP (x, y) = OP Tup ts (toExprP x :< toExprP y :< Ø)
      where
        ts = TP t1 :< TP t2 :< Ø
        t1 = eType (Proxy :: Proxy a)
        t2 = eType (Proxy :: Proxy b)

instance (ToExpr a, ToExpr b) => ToExpr (Either a b) where
    toExpr (Left x)  = o1 Left' (toExpr x)
    toExpr (Right x) = o1 Right' (toExpr x)
    toExprP e = case e of
                  Left x  -> OP Left' ts (only $ toExprP x)
                  Right x -> OP Right' ts (only $ toExprP x)
      where
        ts = TP t1 :< TP t2 :< Ø
        t1 = eType (Proxy :: Proxy a)
        t2 = eType (Proxy :: Proxy b)

-- data ETList :: [*] -> * where
    -- ENil :: ETList '[]
    -- (:*) :: EType a -> ETList as -> ETList (a ': as)

-- infixr 5 :*

-- -- data ExprW :: * where
-- --     EW :: EType a -> Expr '[] a -> ExprW

-- data ExprW :: * where
    -- EW :: ETList vs -> EType a -> Expr vs a -> ExprW

-- -- data ExprIxW :: * -> * where
-- --     EIW :: ETList vs -> Expr vs a -> ExprIxW a

-- data ExprWIx :: [*] -> * where
    -- EWI :: EType a -> Expr vs a -> ExprWIx vs

-- data ETypeW :: * where
    -- ETW :: EType a -> ETypeW

-- deriving instance Show (Indexor ks k)
-- deriving instance Show (Op0 a)
-- deriving instance Show (Op1 a b)
-- deriving instance Show (Op2 a b c)
-- deriving instance Show (Op3 a b c d)
deriving instance Show (EType a)
-- deriving instance Show (ETList a)
-- -- deriving instance Show (ExprIxW a)
-- -- deriving instance Show ExprW'
-- deriving instance Show (ExprWIx a)
-- deriving instance Show ExprW
-- deriving instance Show ETypeW
-- deriving instance Eq (Indexor ks k)
-- deriving instance Eq (Op0 a)
-- deriving instance Eq (Op1 a b)
-- deriving instance Eq (Op2 a b c)
-- deriving instance Eq (Op3 a b c d)
-- -- deriving instance Eq (EType a)
-- -- deriving instance Eq ExprW'

impossible :: String -> a
impossible [] = error "Impossible branch prevented by type system"
impossible str = error $ "Impossible branch prevented by type system: " ++ str


-- instance Num (Expr vs Int) where
    -- (+)         = O2 Plus
    -- (*)         = O2 Times
    -- (-)         = O2 Minus
    -- abs         = O1 Abs
    -- signum      = O1 Signum
    -- fromInteger = O0 . I . fromInteger

-- exprEq :: Expr vs a -> Expr us b -> Bool
-- exprEq (V IZ) (V IZ)                           = True
-- exprEq (V (IS ix1)) (V (IS ix2))               = exprEq (V ix1) (V ix2)
-- exprEq (O0 o1) (O0 o2)                         = op0Eq o1 o2
-- exprEq (O1 o1 e1) (O1 o2 e2)                   = op1Eq o1 o2 && exprEq e1 e2
-- exprEq (O2 o1 e1 e1') (O2 o2 e2 e2')           = op2Eq o1 o2 && exprEq e1 e2 && exprEq e1' e2'
-- exprEq (O3 o1 e1 e1' e1'') (O3 o2 e2 e2' e2'') = op3Eq o1 o2 && exprEq e1 e2 && exprEq e1' e2' && exprEq e1'' e2''
-- exprEq (Lambda f1) (Lambda f2)                 = exprEq f1 f2
-- exprEq _ _                                     = False

-- op0Eq :: Op0 a -> Op0 b -> Bool
-- op0Eq (I i1) (I i2) = i1 == i2
-- op0Eq (B b1) (B b2) = b1 == b2
-- op0Eq Nil    Nil    = True
-- op0Eq Unit   Unit   = True
-- op0Eq _      _      = False

-- op1Eq :: Op1 a b -> Op1 c d -> Bool
-- op1Eq Abs Abs       = True
-- op1Eq Signum Signum = True
-- op1Eq Not Not       = True
-- op1Eq Left' Left'   = True
-- op1Eq Right' Right' = True
-- op1Eq Fst Fst       = True
-- op1Eq Snd Snd       = True
-- op1Eq _   _         = False

-- op2Eq :: Op2 a b c -> Op2 d e f -> Bool
-- op2Eq Plus Plus       = True
-- op2Eq Times Times     = True
-- op2Eq Minus Minus     = True
-- op2Eq LEquals LEquals = True
-- op2Eq And And         = True
-- op2Eq Or Or           = True
-- op2Eq Tup Tup         = True
-- op2Eq Cons Cons       = True
-- op2Eq Ap Ap           = True
-- op2Eq Div Div         = True
-- op2Eq Mod Mod         = True
-- op2Eq _ _             = False

-- op3Eq :: Op3 a b c d -> Op3 e f g h -> Bool
-- op3Eq If If             = True
-- op3Eq Case Case         = True
-- op3Eq UnfoldrN UnfoldrN = True
-- op3Eq Foldr Foldr       = True
-- op3Eq _ _               = False

-- instance Eq (Expr vs a) where
    -- (==) = exprEq

-- instance Eq (HList '[]) where
    -- HNil == HNil = True

-- instance (Eq a, Eq (HList as)) => Eq (HList (a ': as)) where
    -- (x :< xs) == (y :< ys) = x == y && xs == ys

-- eTypeEq :: EType a -> EType b -> Bool
-- eTypeEq a b = case compareEType a b of
    --             EQ -> True
    --             _  -> False

-- instance Eq (EType a) where
    -- (==) = eTypeEq

-- instance Show (Expr vs a) where
    -- showsPrec p e = showParen (p > 10) $ case e of
    --                   V ix -> showString "V "
    --                         . showsPrec 11 ix
    --                   O0 o -> showString "O0 "
    --                         . showsPrec 11 o
    --                   O1 o e1 -> showString "O1 "
    --                            . showsPrec 11 o
    --                            . showString " "
    --                            . showsPrec 11 e1
    --                   O2 o e1 e2 -> showString "O2 "
    --                               . showsPrec 11 o
    --                               . showString " "
    --                               . showsPrec 11 e1
    --                               . showString " "
    --                               . showsPrec 11 e2
    --                   O3 o e1 e2 e3 -> showString "O3 "
    --                                  . showsPrec 11 o
    --                                  . showString " "
    --                                  . showsPrec 11 e1
    --                                  . showString " "
    --                                  . showsPrec 11 e2
    --                                  . showString " "
    --                                  . showsPrec 11 e3
    --                   Lambda ef -> showString "Lambda "
    --                              . showsPrec 11 ef

-- instance Show (HList '[]) where
    -- showsPrec _ HNil = showString "HNil"

-- instance (Show a, Show (HList as)) => Show (HList (a ': as)) where
    -- showsPrec p (x :< xs) = showParen (p > 5) $ showsPrec 6 x
    --                                           . showString " :< "
    --                                           . showsPrec 5 xs

-- compareEType :: EType a -> EType b -> Ordering

-- compareEType EUnit         EUnit         = EQ
-- compareEType EUnit         _             = LT
-- compareEType _             EUnit         = GT
-- compareEType EBool         EBool         = EQ
-- compareEType EBool         _             = LT
-- compareEType _             EBool         = GT
-- compareEType EInt          EInt          = EQ
-- compareEType EInt          _             = LT
-- compareEType _             EInt          = GT
-- compareEType (EEither a b) (EEither c d) = compareEType a b <> compareEType c d
-- compareEType (EEither _ _) _             = LT
-- compareEType _             (EEither _ _) = GT
-- compareEType (ETup a b)    (ETup c d)    = compareEType a b <> compareEType c d
-- compareEType (ETup _ _)    _             = LT
-- compareEType _             (ETup _ _)    = GT
-- compareEType (EFunc a b)   (EFunc c d)   = compareEType a b <> compareEType c d
-- compareEType (EFunc _ _)   _             = LT
-- compareEType _             (EFunc _ _)   = GT
-- compareEType (EList a)     (EList b)     = compareEType a b

-- instance Ord (EType a) where
    -- compare = compareEType

-- instance IsTy EType where
    -- tyEq EUnit EUnit = Just Refl
    -- tyEq EBool EBool = Just Refl
    -- tyEq EInt EInt = Just Refl
    -- tyEq (EList t1) (EList t2) = case tyEq t1 t2 of
    --                                Just Refl -> Just Refl
    --                                _ -> Nothing
    -- tyEq (ETup t1 t1') (ETup t2 t2') = case liftA2 (,) (tyEq t1 t2) (tyEq t1' t2') of
    --                                      Just (Refl, Refl) -> Just Refl
    --                                      _ -> Nothing
    -- tyEq (EEither t1 t1') (EEither t2 t2') = case liftA2 (,) (tyEq t1 t2) (tyEq t1' t2') of
    --                                            Just (Refl, Refl) -> Just Refl
    --                                            _ -> Nothing
    -- tyEq (EFunc t1 t1') (EFunc t2 t2') = case liftA2 (,) (tyEq t1 t2) (tyEq t1' t2') of
    --                                        Just (Refl, Refl) -> Just Refl
    --                                        _ -> Nothing
    -- tyEq _ _ = Nothing


-- -- eTypeSize :: EType a -> Int -> Int
-- -- eTypeSize t = case t of
-- --                 EUnit -> 0 ~~> 1
-- --                 EBool -> 0 ~~> 2
-- --                 EInt  -> 1 ~~> 1
-- --                 EEither a b -> (+) <$> eTypeSize a <*> eTypeSize b
-- --                 ETup a b -> \i -> sum . map (\j -> eTypeSize b j * eTypeSize a (i - j)) $ [0..i]
-- --                 EList a -> eTypeSize a . subtract 1
-- --   where
-- --     (~~>) :: Int -> Int -> Int -> Int
-- --     (i ~~> x) j | j == i    = x
-- --                 | otherwise = 0

-- exprLeafCount :: Expr vs a -> Int
-- exprLeafCount e = case e of
    --                 V _ -> 1
    --                 O0 _ -> 1
    --                 O1 _ e1 -> exprLeafCount e1
    --                 O2 _ e1 e2 -> exprLeafCount e1 + exprLeafCount e2
    --                 O3 _ e1 e2 e3 -> exprLeafCount e1 + exprLeafCount e2 + exprLeafCount e3
    --                 Lambda ef -> exprLeafCount ef

-- exprLeafDepths :: Expr vs a -> [Int]
-- exprLeafDepths e = go 0 e []
  -- where
    -- go :: Int -> Expr vs a -> [Int] -> [Int]
    -- go n e' = case e' of
    --             V _ -> (n:)
    --             O0 _ -> (n:)
    --             O1 _ e1 -> go (n + 1) e1
    --             O2 _ e1 e2 -> go (n + 1) e1 . go (n + 1) e2
    --             O3 _ e1 e2 e3 -> go (n + 1) e1 . go (n + 1) e2 . go (n + 1) e3
    --             Lambda ef -> go (n + 1) ef


curry'1 :: (Prod f '[a] -> c) -> f a -> c
curry'1 f x = f (x :< Ø)

curry'2 :: (Prod f '[a,b] -> c) -> f a -> f b -> c
curry'2 f x y = f (x :< y :< Ø)

curry'3 :: (Prod f '[a,b,c] -> d) -> f a -> f b -> f c -> d
curry'3 f x y z = f (x :< y :< z :< Ø)

uncurry'1 :: (f a -> f c) -> Prod f '[a] -> f c
uncurry'1 f (x :< Ø) = f x

uncurry'2 :: (f a -> f b -> f c) -> Prod f '[a, b] -> f c
uncurry'2 f (x :< y :< Ø) = f x y

uncurry'3 :: (f a -> f b -> f c -> f d) -> Prod f '[a, b, c] -> f d
uncurry'3 f (x :< y :< z :< Ø) = f x y z


-- curryProd3 :: (Prod f '[a,b,c] -> c) -> f a -> f b -> c
-- curryProd3 f x y = f (x :< y :< Ø)

o0 :: Op0 ts a -> Expr vs a
o0 = flip O Ø

o1 :: Op1 ts a b -> Expr vs a -> Expr vs b
o1 o = curry'1 (O o)

o2 :: Op2 ts a b c -> Expr vs a -> Expr vs b -> Expr vs c
o2 o = curry'2 (O o)

o3 :: Op3 ts a b c d -> Expr vs a -> Expr vs b -> Expr vs c -> Expr vs d
o3 o = curry'3 (O o)

-- type family CurryProd f ts r where
--   CurryProd f '[]       r = r
--   CurryProd f (t ': ts) r = f t -> CurryProd f ts r

-- curryProd :: (Prod f ts -> r) -> CurryProd f ts r
-- curryProd f x = undefined

infixl 1 ~$

(~$) :: Expr vs (a -> b) -> Expr vs a -> Expr vs b
(~$) = o2 Ap

foldr' :: Expr vs (a -> b -> b) -> Expr vs b -> Expr vs [a] -> Expr vs b
foldr' = o3 Foldr

case' :: Expr vs (Either a b) -> Expr vs (a -> c) -> Expr vs (b -> c) -> Expr vs c
case' = o3 Case

unfoldrN' :: Expr vs Int -> Expr vs (a -> (b, a)) -> Expr vs a -> Expr vs [b]
unfoldrN' = o3 UnfoldrN

if' :: Expr vs Bool -> Expr vs a -> Expr vs a -> Expr vs a
if' = o3 If

right' :: Expr vs b -> Expr vs (Either a b)
right' = o1 Right'

left' :: Expr vs a -> Expr vs (Either a b)
left' = o1 Left'

just' :: Expr vs b -> Expr vs (Maybe' b)
just' = right'

nothing' :: Expr vs (Maybe' b)
nothing' = left' unit'

tup' :: Expr vs a -> Expr vs b -> Expr vs (a, b)
tup' = o2 Tup

fst' :: Expr vs (a, b) -> Expr vs a
fst' = o1 Fst

snd' :: Expr vs (a, b) -> Expr vs b
snd' = o1 Snd

infixr 3 ~&&
(~&&) :: Expr vs Bool -> Expr vs Bool -> Expr vs Bool
(~&&) = o2 And

infixr 2 ~||
(~||) :: Expr vs Bool -> Expr vs Bool -> Expr vs Bool
(~||) = o2 Or

infix 4 ~<=
(~<=) :: Expr vs Int -> Expr vs Int -> Expr vs Bool
(~<=) = o2 LEquals

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
not' = o1 Not

xor' :: Expr vs Bool -> Expr vs Bool -> Expr vs Bool
xor' e1 e2 = (e1 ~|| e2) ~&& not' (e1 ~&& e2)

infixl 7 `mod'`
mod' :: Expr vs Int -> Expr vs Int -> Expr vs (Maybe' Int)
mod' = o2 Mod

infixl 7 `div'`
div' :: Expr vs Int -> Expr vs Int -> Expr vs (Maybe' Int)
div' = o2 Div

infixr 5 ~:
(~:) :: Expr vs a -> Expr vs [a] -> Expr vs [a]
(~:) = o2 Cons

unit' :: Expr vs ()
unit' = o0 Unit

nil' :: Expr vs [a]
nil' = o0 Nil

false' :: Expr vs Bool
false' = o0 (B False)

true' :: Expr vs Bool
true' = o0 (B True)

iI :: Int -> Expr vs Int
iI = o0 . I

bB :: Bool -> Expr vs Bool
bB = o0 . B

λ :: Expr (a ': vs) b -> Expr vs (a -> b)
λ = Lambda

infixr 0 .->
(.->) :: (Expr (a ': vs) b -> Expr vs (a -> b)) -> Expr (a ': vs) b -> Expr vs (a -> b)
(.->) = ($)

-- isEEither :: EType a -> Bool
-- isEEither (EEither _ _) = True
-- isEEither _ = False

-- isEFunc :: EType a -> Bool
-- isEFunc (EFunc _ _) = True
-- isEFunc _ = False

-- isCompoundType :: EType a -> Bool
-- isCompoundType (EEither _ _) = True
-- isCompoundType (ETup _ _) = True
-- isCompoundType (EFunc _ _) = True
-- isCompoundType (EList _) = True
-- isCompoundType _ = False

-- eTypeLeaves :: EType a -> Int
-- eTypeLeaves EInt = 1
-- eTypeLeaves EBool = 1
-- eTypeLeaves EUnit = 1
-- eTypeLeaves (EList x) = eTypeLeaves x
-- eTypeLeaves (EEither x y) = eTypeLeaves x + eTypeLeaves y
-- eTypeLeaves (ETup x y) = eTypeLeaves x + eTypeLeaves y
-- eTypeLeaves (EFunc x y) = eTypeLeaves x + eTypeLeaves y

-- eTypeNodes :: EType a -> Int
-- eTypeNodes EInt = 1
-- eTypeNodes EBool = 1
-- eTypeNodes EUnit = 1
-- eTypeNodes (EList x) = 1 + eTypeLeaves x
-- eTypeNodes (EEither x y) = 1 + eTypeLeaves x + eTypeLeaves y
-- eTypeNodes (ETup x y) = 1 + eTypeLeaves x + eTypeLeaves y
-- eTypeNodes (EFunc x y) = 1 + eTypeLeaves x + eTypeLeaves y

-- eTypeDepth :: EType a -> Int
-- eTypeDepth EInt = 0
-- eTypeDepth EBool = 1
-- eTypeDepth EUnit = 0
-- eTypeDepth (EList x) = 1 + eTypeDepth x
-- eTypeDepth (EEither x y) = 1 + max (eTypeDepth x) (eTypeDepth y)
-- eTypeDepth (ETup x y) = 1 + max (eTypeDepth x) (eTypeDepth y)
-- eTypeDepth (EFunc x y) = 1 + max (eTypeDepth x) (eTypeDepth y)

-- absurdIxor :: Indexor '[] a -> b
-- absurdIxor ix = ix `seq` let x = x in x

-- indexorLength :: Indexor vs a -> Int
-- indexorLength IZ = 0
-- indexorLength (IS ix) = 1 + indexorLength ix

-- enumTypes :: [ETypeW]
-- enumTypes = concatMap enumTypesD [0..]

-- enumTypesD :: Int -> [ETypeW]
-- enumTypesD n | n <= 0 = [ETW EInt, ETW EBool, ETW EUnit]
    --          | otherwise = mkList ++ mkOthers
  -- where
    -- mkList = do
    --   ETW t1 <- enumTypesD (n - 1)
    --   return $ ETW (EList t1)
    -- mkOthers = do
    --   ETW t1 <- enumTypesD (n - 1)
    --   ETW t2 <- enumTypesD (n - 1)
    --   [ETW (EEither t1 t2), ETW (ETup t1 t2), ETW (EFunc t1 t2)]
