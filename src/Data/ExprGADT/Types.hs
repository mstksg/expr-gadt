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
{-# LANGUAGE PatternSynonyms #-}

module Data.ExprGADT.Types where

-- import Control.Applicative
-- import Data.IsTy
-- import Data.Monoid
-- import Data.Proof.EQ
import Data.Proxy
import Data.Type.Combinator hiding (I)
import qualified Data.Type.Combinator as C (I)
import Data.Type.Fin
import Data.Type.Product
import Data.Type.Vector
import Type.Family.List       as L
import Type.Family.Nat

data Indexor :: [k] -> k -> * where
    IZ :: Indexor (k ': ks) k
    IS :: Indexor ks k -> Indexor (j ': ks) k

type ETList = Prod EType
type ExprList vs = Prod (Expr vs)

type ExprPList vs = Prod (ExprP vs)
type ExprPET vs a = ExprP vs (EType a)
type ExprPETList vs ts = Prod (ExprP vs :.: EType) ts

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
    TP       :: TOp as a -> ExprPETList vs as -> ExprP vs (EType a)
    OP       :: Op ts as a -> ExprPETList vs ts -> ExprPList vs as -> ExprP vs a
    LambdaP  :: ExprP vs (EType a) -> ExprP (a ': vs) b -> ExprP vs (a -> b)

data ExprTy :: N -> * where
    VTy :: Fin n -> ExprTy n
    TTy :: TOp as a -> V (LengthList as) (ExprTy n) -> ExprTy n
    Forall :: ExprTy (S n) -> ExprTy n
    -- ApTy :: ExprTy (S n) -> ExprTy n -> ExprTy n

    -- TT :: TOp as a -> Prod (ExprT vs) (EType L.<$> as) -> ExprT vs a
    -- -- this doesn't make any sense?
    -- LambdaT :: ExprT as a -> ExprT (EType a ': as) b -> ExprT vs (a -> b)

type family LengthList (as :: [k]) :: N where
    LengthList '[] = Z
    LengthList (a ': as) = S (LengthList as)

-- data ExprT :: [*] -> * -> * where
--     VT :: Indexor vs (EType a) -> ExprT vs a
--     TT :: TOp as a -> Prod (ExprT vs) (EType L.<$> as) -> ExprT vs a
--     -- this doesn't make any sense?
--     LambdaT :: ExprT as a -> ExprT (EType a ': as) b -> ExprT vs (a -> b)

testNil :: ExprP vs (EType a -> [a])
testNil = LambdaP (TP TOStar Ø) (OP Nil (only (Comp $ VP i1)) Ø)

testId :: ExprP vs (EType a -> a -> a)
testId = LambdaP (TP TOStar Ø) (LambdaP (VP i1) (VP i1))

testConst :: ExprP vs (EType a -> EType b -> a -> b -> a)
testConst = LambdaP (TP TOStar Ø)
          $ LambdaP (TP TOStar Ø)
          $ LambdaP (VP i2)
          $ LambdaP (VP i2)
          $ VP i2

testComp :: ExprP vs (EType a -> EType b -> EType c -> (b -> c) -> (a -> b) -> a -> c)
testComp = LambdaP (TP TOStar Ø)
         $ LambdaP (TP TOStar Ø)
         $ LambdaP (TP TOStar Ø)
         $ LambdaP (TP TOFunc (Comp (VP i2) :> Comp (VP i1)))
         $ LambdaP (TP TOFunc (Comp (VP i4) :> Comp (VP i3)))
         $ LambdaP (VP i5)
         $ O2p Ap (Comp (VP i5) :> Comp (VP i4)) (VP i3)
         $ O2p Ap (Comp (VP i6) :> Comp (VP i5)) (VP i2) (VP i1)

i1 :: Indexor (j ': js) j
i1 = IZ

i2 :: Indexor (j ': k ': ks) k
i2 = IS i1

i3 :: Indexor (j ': k ': l ': ls) l
i3 = IS i2

i4 :: Indexor (j ': k ': l ': m ': ms) m
i4 = IS i3

i5 :: Indexor (j ': k ': l ': m ': n ': ns) n
i5 = IS i4

i6 :: Indexor (j ': k ': l ': m ': n ': o ': os) o
i6 = IS i5

i7 :: Indexor (j ': k ': l ': m ': n ': o ': p ': ps) p
i7 = IS i6



testComp' :: Expr vs ((b -> c) -> (a -> b) -> a -> c)
testComp' = Lambda
          $ Lambda
          $ Lambda
          $ O2 Ap (V (IS (IS IZ))) (O2 Ap (V (IS IZ)) (V IZ))

type Maybe' = Either ()

data TOp :: [*] -> * -> * where
    TOStar   :: TOp '[] (EType a)
    TOInt    :: TOp '[] Int
    TOBool   :: TOp '[] Bool
    TOUnit   :: TOp '[] ()
    TOList   :: TOp '[a] [a]
    TOEither :: TOp '[a, b] (Either a b)
    TOTup    :: TOp '[a, b] (a, b)
    TOFunc   :: TOp '[a, b] (a -> b)

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

fromEType :: EType a -> ExprP vs (EType a)
fromEType EInt = TP TOInt Ø
fromEType EBool = TP TOBool Ø
fromEType EUnit = TP TOUnit Ø
fromEType (EList a) = TP TOList (only (fromEType' a))
fromEType (EEither a b) = TP TOEither (fromEType' a :> fromEType' b)
fromEType (ETup a b) = TP TOTup (fromEType' a :> fromEType' b)
fromEType (EFunc a b) = TP TOFunc (fromEType' a :> fromEType' b)

fromEType' :: EType a -> (ExprP vs :.: EType) a
fromEType' = Comp . fromEType

eType' :: HasEType a => p a -> ExprP vs (EType a)
eType' = fromEType . eType

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
    toExpr = O0 . I
    toExprP i = OP (I i) Ø Ø

instance ToExpr Bool where
    toExpr = O0 . B
    toExprP b = OP (B b) Ø Ø

instance ToExpr () where
    toExpr _ = O0 Unit
    toExprP _ = OP Unit Ø Ø

instance ToExpr a => ToExpr [a] where
    toExpr []     = O0 Nil
    toExpr (x:xs) = O2 Cons (toExpr x) (toExpr xs)
    toExprP xs = case xs of
                   []   -> OP Nil t Ø
                   y:ys -> OP Cons t (toExprP y :< toExprP ys :< Ø)
      where
        t = only . fromEType' $ eType (Proxy :: Proxy a)

instance (ToExpr a, ToExpr b) => ToExpr (a, b) where
    toExpr (x, y) = O2 Tup (toExpr x) (toExpr y)
    toExprP (x, y) = OP Tup ts (toExprP x :< toExprP y :< Ø)
      where
        ts = Comp t1 :< Comp t2 :< Ø
        t1 = eType' (Proxy :: Proxy a)
        t2 = eType' (Proxy :: Proxy b)

instance (ToExpr a, ToExpr b) => ToExpr (Either a b) where
    toExpr (Left x)  = O1 Left' (toExpr x)
    toExpr (Right x) = O1 Right' (toExpr x)
    toExprP e = case e of
                  Left x  -> OP Left' ts (only $ toExprP x)
                  Right x -> OP Right' ts (only $ toExprP x)
      where
        ts = Comp t1 :< Comp t2 :< Ø
        t1 = eType' (Proxy :: Proxy a)
        t2 = eType' (Proxy :: Proxy b)

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

data ETypeW :: * where
    ETW :: EType a -> ETypeW

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

deriving instance Show (ExprTy n)
deriving instance Show (TOp as a)

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
-- exprEq (O0 O1) (O0 O2)                         = op0Eq O1 O2
-- exprEq (O1 O1 e1) (O1 O2 e2)                   = op1Eq O1 O2 && exprEq e1 e2
-- exprEq (O2 O1 e1 e1') (O2 O2 e2 e2')           = op2Eq O1 O2 && exprEq e1 e2 && exprEq e1' e2'
-- exprEq (O3 O1 e1 e1' e1'') (O3 O2 e2 e2' e2'') = op3Eq O1 O2 && exprEq e1 e2 && exprEq e1' e2' && exprEq e1'' e2''
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

pattern O0 :: Op0 ts a -> Expr vs a
pattern O0 o = O o Ø

pattern O1 :: Op1 ts a b -> Expr vs a -> Expr vs b
pattern O1 o e1 = O o (e1 :< Ø)

pattern O2 :: Op2 ts a b c -> Expr vs a -> Expr vs b -> Expr vs c
pattern O2 o e1 e2 = O o (e1 :< e2 :< Ø)

pattern O3 :: Op3 ts a b c d -> Expr vs a -> Expr vs b -> Expr vs c -> Expr vs d
pattern O3 o e1 e2 e3 = O o (e1 :< e2 :< e3 :< Ø)

pattern O0p :: Op0 ts a -> ExprPETList vs ts -> ExprP vs a
pattern O0p o ts = OP o ts Ø

pattern O1p :: Op1 ts a b -> ExprPETList vs ts -> ExprP vs a -> ExprP vs b
pattern O1p o ts e1 = OP o ts (e1 :< Ø)

pattern O2p :: Op2 ts a b c -> ExprPETList vs ts -> ExprP vs a -> ExprP vs b -> ExprP vs c
pattern O2p o ts e1 e2 = OP o ts (e1 :< e2 :< Ø)

pattern O3p :: Op3 ts a b c d -> ExprPETList vs ts -> ExprP vs a -> ExprP vs b -> ExprP vs c -> ExprP vs d
pattern O3p o ts e1 e2 e3 = OP o ts (e1 :< e2 :< e3 :< Ø)


-- type family CurryProd f ts r where
--   CurryProd f '[]       r = r
--   CurryProd f (t ': ts) r = f t -> CurryProd f ts r

-- curryProd :: (Prod f ts -> r) -> CurryProd f ts r
-- curryProd f x = undefined

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
