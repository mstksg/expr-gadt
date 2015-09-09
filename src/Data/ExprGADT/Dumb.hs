{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}

module Data.ExprGADT.Dumb where

import Data.ExprGADT.Dumb.Types
import Data.ExprGADT.Types
import Data.Typeable
import Data.ExprGADT.Traversals
import Control.Exception
import Data.Map.Strict           (Map)
import Data.Singletons.Decide
import Data.Proxy
import Control.Monad.Except
import Data.Singletons
import Data.Proof.EQ as Ty
import Data.IsTy
import Data.Singletons.TH
import Data.Singletons.Prelude hiding (Map)
import Unsafe.Coerce
import Control.Applicative
import Data.Maybe
import qualified Data.Map.Strict as M

$(singletons [d|
    data PNat = NZ | NS PNat deriving (Eq, Show, Ord)

    nPlus :: PNat -> PNat -> PNat
    nPlus NZ     y = y
    nPlus (NS x) y = NS (nPlus x y)

    |])

data Vec :: PNat -> * -> * where
    VNil :: Vec 'NZ a
    (:>) :: a -> Vec n a -> Vec ('NS n) a

infixr 5 :>

instance Functor (Vec n) where
    fmap _ VNil = VNil
    fmap f (x :> xs) = f x :> fmap f xs

concatVec :: forall n m a. Vec n a -> Vec m a -> Vec (NPlus n m) a
concatVec VNil      y = y
concatVec (x :> xs) y = x :> concatVec xs y

data NatIxor :: PNat -> * where
    NIZ :: NatIxor ('NS n)
    NIS :: NatIxor n -> NatIxor ('NS n)

deriving instance Eq (NatIxor n)
deriving instance Ord (NatIxor n)

type family NComp (n :: PNat) (m :: PNat) :: Ordering where
    NComp 'NZ 'NZ = 'EQ
    NComp n 'NZ = 'GT
    NComp 'NZ m = 'LT
    NComp ('NS n) ('NS m) = NComp n m

indexVec :: Vec n a -> NatIxor n -> a
indexVec (x :> _ ) NIZ     = x
indexVec (_ :> xs) (NIS i) = indexVec xs i
indexVec VNil _ = error "come on ghc..."

takeVec :: Sing n -> Vec m a -> Maybe (Vec n a)
takeVec SNZ _             = Just VNil
takeVec (SNS n) (x :> xs) = (x :>) <$> takeVec n xs
takeVec (SNS _) VNil      = Nothing

applyOnLast :: (Vec m a -> b) -> Sing n -> Vec (NPlus n m) a -> b
applyOnLast f SNZ xs = f xs
applyOnLast f (SNS i) (_ :> xs) = applyOnLast f i xs
applyOnLast _ (SNS _) _ = error "impossible...cannot be called."

shiftNIx :: Sing n -> NatIxor m -> NatIxor (NPlus n m)
shiftNIx = undefined

data TypeError = TErrUniFail
               | TErrInfType
               | TErrUnboundVar VName

data TExpr :: PNat -> PNat -> * where
    TEVB     :: NatIxor b -> TExpr b u
    TEVU     :: NatIxor u -> TExpr b u
    TEO0     :: TOp0 -> TExpr b u
    TEO1     :: TOp1 -> TExpr b u -> TExpr b u
    TEO2     :: TOp2 -> TExpr b u -> TExpr b u -> TExpr b u
    TEForall :: TExpr b ('NS u) -> TExpr ('NS b) u
    -- TESub    :: TExpr b ('NS u) -> TExpr b u -> TExpr b u

type TExpr' = TExpr 'NZ

fromTExpr :: forall a b u.
             (NatIxor b -> a)
          -> (NatIxor u -> a)
          -> (TOp0 -> a)
          -> (TOp1 -> a -> a)
          -> (TOp2 -> a -> a -> a)
          -> TExpr b u
          -> a
fromTExpr fb fu f0 f1 f2 = go
  where
    go :: TExpr b u -> a
    go e = case e of
             TEVB i       -> fb i
             TEVU i       -> fu i
             TEO0 o       -> f0 o
             TEO1 o e1    -> f1 o (go e1)
             TEO2 o e1 e2 -> f2 o (go e1) (go e2)
             TEForall e1  -> let fb' :: (b ~ 'NS b') => NatIxor b' -> a
                                 fb' i = fb (NIS i)
                                 fu' :: NatIxor ('NS u) -> a
                                 fu' NIZ     = fb NIZ
                                 fu' (NIS i) = fu i
                             in  fromTExpr fb' fu' f0 f1 f2 e1
             -- TESub e1 t  -> fromTExpr bs (t :> us) f0 f1 f2 e1

tExprToETW :: Vec b ETypeW -> Vec u ETypeW -> TExpr b u -> ETypeW
tExprToETW bs us = fromTExpr (indexVec bs) (indexVec us) f0 f1 f2
  where
    f0 o = case o of
             TOInt  -> ETW EInt
             TOBool -> ETW EBool
             TOUnit -> ETW EUnit
    f1 TOList (ETW t) = ETW (EList t)
    f2 o (ETW t1) (ETW t2) =
            case o of
              TOTuple -> ETW (ETup t1 t2)
              TOEither -> ETW (EEither t1 t2)
              TOFunc -> ETW (EFunc t1 t2)

data TExprBW :: PNat -> * where
    TEBW :: Sing b -> TExpr b u -> TExprBW u

data Env :: PNat -> * where
    Env :: Map VName (TExprBW u) -> Env u

extendEnv :: VName -> TExprBW u -> Env u -> Env u
extendEnv v t (Env m) = Env $ M.insert v t m

data Subst :: PNat -> PNat -> * where
    Subst :: (NatIxor u -> TExpr' v) -> Subst u v

nullSubst :: Subst u u
nullSubst = Subst TEVU

composeSubst :: forall u v w. Subst u v -> Subst v w -> Subst u w
composeSubst (Subst f) (Subst g) = Subst h
  where
    h :: NatIxor u -> TExpr' w
    h = fromTExpr (impossible "") g TEO0 TEO1 TEO2 . f

unify :: TExpr' u -> TExpr' u -> Either TypeError (Subst u u)
unify (TEO0 o) (TEO0 o') | o == o' = return nullSubst
unify (TEO1 o t) (TEO1 o' t') | o == o' = unify t t'
unify (TEO2 o t s) (TEO2 o' t' s') | o == o' = do
    subt <- unify t t'
    subs <- unify s s'
    return $ composeSubst subt subs
unify (TEVU v) t = bind v t
unify t (TEVU v) = bind v t
unify (TEVB _) (TEVB _) = impossible ""
unify _ _ = throwError TErrUniFail

bind :: forall u. NatIxor u -> TExpr' u -> Either TypeError (Subst u u)
bind v t = case t of
             TEVU v' | v == v'       -> return nullSubst
             _       | occursCheck t -> throwError TErrInfType
                     | otherwise     -> return (singleSubst v t)
  where
    occursCheck :: TExpr' u -> Bool
    occursCheck (TEO0 _) = False
    occursCheck (TEO1 _ t1) = occursCheck t1
    occursCheck (TEO2 _ t1 t2) = occursCheck t1 || occursCheck t2
    occursCheck (TEVU v') = v == v'
    occursCheck (TEVB _) = impossible ""

-- should really be Subst ('NS u) u, but?  need arb-conversion of NatIxor
-- too lazy atm.
singleSubst :: NatIxor u -> TExpr' u -> Subst u u
singleSubst v t = Subst $ \i -> if v == i then t
                                          else TEVU i

-- data PolyExpr :: [*] -> * where
--     PE :: Sing n -> (Vec n ETypeW -> ExprWIx vs) -> PolyExpr vs

data PolyExpr :: * where
    PE :: Sing n -> (Vec n ETypeW -> ExprW) -> PolyExpr

-- unDumbWith :: Env u -> Vec u ETypeW -> DumbExpr -> PolyExpr
-- unDumbWith env us e = case e of
--                         TEVU

-- data UnDumb :: * where
--     EWT :: TExpr b u -> ()

-- dropIn :: a -> NatIxor n -> NatIxor ('NS m) -> Either a (NatIxor m)
-- dropIn x i p = case p of
--                  NIS ip -> undefined

-- infer :: forall u. Env u -> DumbExpr -> Either TypeError (Subst u u, TExprBW u)
-- infer env@(Env mp) e =
--     case e of
--       DV v -> case M.lookup v mp of
--                 Nothing -> throwError $ TErrUnboundVar v
--                 Just t  -> return (nullSubst, t)
--       DLambda v e1 -> do
--         let env' = extendEnv v (TEBW SNZ fresh) (bumpUp env)
--         (s1, t1) <- infer env' e1
--         return $ (s1, undefined)
--   where
--     bumpUp :: Env v -> Env ('NS v)
--     bumpUp = undefined
-- -- extendEnv :: SingI b => VName -> TExpr b u -> Env u -> Env u

    -- DLambda :: VName        -> DumbExpr -> DumbExpr

-- fresh :: TExpr' ('NS n)
-- fresh = TEVU NIZ


-- data TExpr :: PNat -> * where
--     TEV :: NatIxor v -> TExpr v
--     TEO0 :: TOp0 -> TExpr v
--     TEO1 :: TOp1 -> TExpr v -> TExpr v
--     TEO2 :: TOp2 -> TExpr v -> TExpr v -> TExpr v
--     TEForall :: TExpr ('NS v) -> TExpr v

-- data PolyType :: * where
--     PT :: Sing n -> (Vec n ETypeW -> ETypeW) -> PolyType

-- data PolyTExpr :: PNat -> * where
--     PTE :: Sing n -> (Vec n (TExpr m) -> TExpr m) -> PolyTExpr m

-- fromTExpr :: forall v. (NatIxor v -> ETypeW) -> TExpr v -> PolyType
-- fromTExpr f (TEV i) = PT SNZ (\_ -> f i)
-- fromTExpr _ (TEO0 o) =
--     case o of
--       TOInt  -> PT SNZ (\_ -> ETW EInt)
--       TOBool -> PT SNZ (\_ -> ETW EBool)
--       TOUnit -> PT SNZ (\_ -> ETW EUnit)
-- fromTExpr f (TEO1 o e1) =
--     case fromTExpr f e1 of
--       PT n g -> PT n $ \ts ->
--         case g ts of
--           ETW t -> case o of
--                      TOList -> ETW (EList t)
-- fromTExpr f (TEO2 o e1 e2) =
--     case (fromTExpr f e1, fromTExpr f e2) of
--       (PT n1 g1, PT n2 g2) ->
--         PT (sNPlus n1 n2) $ \ts ->
--           let Just etw1 = g1 <$> takeVec n1 ts
--               etw2 = applyOnLast g2 n1 ts
--           in  case (etw1, etw2) of
--                 (ETW t1, ETW t2) -> case o of
--                                       TOTuple -> ETW (ETup t1 t2)
--                                       TOEither -> ETW (EEither t1 t2)
--                                       TOFunc -> ETW (EFunc t1 t2)
-- fromTExpr f (TEForall eλ) = undefined
--   where
--     breakDown :: TExpr ('NS u) -> PolyTExpr u
--     breakDown (TEV NIZ)      = PTE (SNS SNZ) (\(t :> VNil) -> t)
--     breakDown (TEV (NIS i))  = PTE SNZ (\VNil -> TEV i)
--     breakDown (TEO0 o)       = PTE SNZ (\VNil -> TEO0 o)
--     breakDown (TEO1 o e1)    = case breakDown e1 of
--                                  PTE n g -> PTE n (TEO1 o . g)
--     breakDown (TEO2 o e1 e2) = case (breakDown e1, breakDown e2) of
--                                  (PTE n1 g1, PTE n2 g2) ->
--                                    PTE (sNPlus n1 n2) $ \ts ->
--                                      let Just ts1 = g1 <$> takeVec n1 ts
--                                          ts2      = applyOnLast g2 n1 ts
--                                      in  TEO2 o ts1 ts2
--     breakDown (TEForall eλ') = case breakDown eλ' of
--                                  PTE n g -> PTE (SNS n) $ \(t :> ts) ->
--                                    undefined
    -- breakDown (TEV i) = PT SNZ (\VNil -> i)
    -- let f' :: NatIxor ('NS v) -> ETypeW
    --     f' NIZ = undefined
    --     f' (NIS i) = f i
    -- in  case fromTExpr f e1 of
    --       _ -> undefined
          -- PT n g -> PT (SNS n) $ \(ETW t :> ts) ->
          --   g ts



-- unshiftNIx :: NatIxor m -> NatIxor (NPlus m n)
-- unshiftNIx :: NatIxor n -> NatIxor (NPlus m n)
-- unshiftNIx NIZ = NIZ

-- data Subst :: * where
--     Subst :: Sing n -> Map VName (NatIxor n) -> Vec n TExpr -> Subst

-- nullSubst :: Subst
-- nullSubst = Subst SNZ M.empty VNil

-- singleSubst :: TVar -> TExpr -> Subst
-- singleSubst (TV v) t = Subst (SNS SNZ) (M.singleton v NIZ) (t :> VNil)

-- composeSubst :: Subst -> Subst -> Subst
-- composeSubst (Subst (n1 :: Sing n) m1 v1)
--              (Subst (n2 :: Sing m) m2 v2)
--            = Subst (sNPlus n1 n2) mp (concatVec v1 (fmap apl v2))
--   where
--     apl :: TExpr -> TExpr
--     apl (TEO0 t) = TEO0 t
--     apl (TEO1 o t) = TEO1 o (apl t)
--     apl (TEO2 o t t') = TEO2 o (apl t) (apl t')
--     apl te@(TEV (TV v)) = maybe te (indexVec v1) $ M.lookup v m1
--     mp :: Map VName (NatIxor (NPlus n m))
--     mp = fmap coerceNIx m1 `M.union` fmap (shiftNIx n1) m2
--     coerceNIx :: forall q. NatIxor q -> NatIxor (NPlus q m)
--     coerceNIx NIZ     = NIZ
--     coerceNIx (NIS i) = NIS (coerceNIx i)

-- unify :: TExpr -> TExpr -> Either TypeError Subst
-- unify (TEV v) t = bind v t
-- unify t (TEV v) = bind v t
-- unify (TEO0 t) (TEO0 t')      | Just Ty.Refl <- tyEq t t' = return  nullSubst
-- unify (TEO1 o t) (TEO1 o' t') | o == o' = unify t t'
-- unify (TEO2 o t u) (TEO2 o' t' u') | o == o' = do
--     st <- unify t t'
--     su <- unify u u'
--     return $ composeSubst st su
-- unify t u = throwError $ TErrUniFail t u

-- bind :: TVar -> TExpr -> Either TypeError Subst
-- bind v t | t == TEV v    = return nullSubst
--          | occursCheck t = throwError $ TErrInfType v t
--          | otherwise     = return (singleSubst v t)
--   where
--     occursCheck (TEO0 _)        = False
--     occursCheck (TEO1 _ t')     = occursCheck t'
--     occursCheck (TEO2 _ t' t'') = occursCheck t' || occursCheck t''
--     occursCheck (TEV v')        = v == v'

-- -- data Scheme :: * where
-- --     Forall :: Sing n -> (Vec n ETypeW -> TExpr)
--     -- Subst :: Sing n -> Map VName (NatIxor n) -> Vec n TExpr -> Subst

-- data Env = Env
-- data PolyExpr = PolyExpr

-- unDumbWith :: Env -> DumbExpr -> Either TypeError PolyExpr
-- unDumbWith = undefined

-- data PolyType :: * where
--     PT :: Sing n -> (Vec n ETypeW -> ETypeW) -> PolyType

-- data PNat :: * where
--     NZ :: PNat
--     NS :: PNat -> PNat
--   deriving (Eq, Ord, Show)

-- data instance Sing (n :: PNat) where
--     SNZ :: Sing 'NZ
--     SNS :: Sing (m :: PNat) -> Sing ('NS m)

-- deriving instance Show (Sing (n :: PNat))

-- data Vec :: PNat -> * -> * where
--     VNil :: Vec 'NZ a
--     (:>) :: a -> Vec n a -> Vec ('NS n) a

-- infixr 5 :>

-- instance Functor (Vec n) where
--     fmap _ VNil = VNil
--     fmap f (x :> xs) = f x :> fmap f xs

-- instance Applicative (Vec 'NZ) where
--     pure _ = VNil
--     _ <*> _ = VNil

-- instance Applicative (Vec n) => Applicative (Vec ('NS n)) where
--     pure x = x :> pure x
--     (f :> fx) <*> (x :> xs) = f x :> (fx <*> xs)

-- type family NPlus (n :: PNat) (m :: PNat) :: PNat where
--     NPlus 'NZ m = m
--     NPlus ('NS n) m = 'NS (NPlus n m)

-- addSN :: forall n m nm. (NPlus n m ~ nm)
--       => Sing n -> Sing m -> Sing nm
-- addSN SNZ y = y
-- addSN (SNS x) y = SNS (addSN x y)

-- concatVec :: forall n m a. Vec n a -> Vec m a -> Vec (NPlus n m) a
-- concatVec VNil      y = y
-- concatVec (x :> xs) y = x :> concatVec xs y

-- type family NSub (n :: PNat) (m :: PNat) :: PNat where
--     NSub n      'NZ      = 'NZ
--     NSub 'NZ     m       = m
--     NSub ('NS n) ('NS m)  = NSub n m

-- subSN :: forall n m nm. (NSub n m ~ nm)
--       => Sing n -> Sing m -> Sing nm
-- subSN _ SNZ = SNZ
-- subSN SNZ y = y
-- subSN (SNS x) (SNS y) = subSN x y

-- type family NComp (n :: PNat) (m :: PNat) :: Ordering where
--     NComp 'NZ 'NZ = 'EQ
--     NComp n 'NZ = 'GT
--     NComp 'NZ m = 'LT
--     NComp ('NS n) ('NS m) = NComp n m

-- type family NMin (n :: PNat) (m :: PNat) :: PNat where
--     NMin n 'NZ = 'NZ
--     NMin 'NZ m = 'NZ
--     NMin ('NS n) ('NS m) = 'NS (NMin n m)

-- instance SingI 'NZ where
--     sing = SNZ

-- instance SingI n => SingI ('NS n) where
--     sing = SNS sing

-- takeVec :: Sing n -> Vec m a -> Maybe (Vec n a)
-- takeVec SNZ _             = Just VNil
-- takeVec (SNS n) (x :> xs) = (x :>) <$> takeVec n xs
-- takeVec (SNS _) VNil      = Nothing

-- applyOnLast :: (Vec m a -> b) -> Sing n -> Vec (NPlus n m) a -> b
-- applyOnLast f SNZ xs = f xs
-- applyOnLast f (SNS i) (_ :> xs) = applyOnLast f i xs
-- applyOnLast _ (SNS _) _ = error "impossible...cannot be called."

-- collapseTExpr :: TExpr -> PolyType
-- collapseTExpr (TEV _)  = PT (SNS SNZ) (\(t :> VNil) -> t)    -- todo
-- collapseTExpr (TEO0 t) = PT SNZ (\VNil -> ETW t)
-- collapseTExpr (TEO1 o t1) = case collapseTExpr t1 of
--                               PT n f ->
--                                 case o of
--                                   TOList -> PT n $ \ts ->
--                                               case f ts of
--                                                 ETW t -> ETW (EList t)
-- collapseTExpr (TEO2 o t1 t2) = case (collapseTExpr t1, collapseTExpr t2) of
--                                  (PT (n :: Sing n) f, PT (m :: Sing m) g) ->
--                                    PT (addSN n m) $ \(ts :: Vec (NPlus n m) ETypeW) ->
--                                      let Just etw1 = f <$> takeVec n ts
--                                          etw2 = applyOnLast g n ts
--                                      in  case (etw1, etw2) of
--                                            (ETW t1', ETW t2') -> case o of
--                                                                    TOEither -> ETW (EEither t1' t2')
--                                                                    TOTuple -> ETW (ETup t1' t2')
--                                                                    TOFunc -> ETW (EFunc t1' t2')

-- type family CompIx (as :: [k]) (n :: PNat) :: Ordering where
--     CompIx '[] 'NZ = 'EQ
--     CompIx '[] x   = 'LT
--     CompIx xs  'NZ = 'GT
--     CompIx (x ': xs) ('NS i) = CompIx xs i

-- data UDEnv :: [*] -> * where
--     UDE :: (CompIx vs ('NS n) ~ 'LT) => Map VName (NatIxor n) -> ETList vs -> UDEnv vs

-- data NatIxor :: PNat -> * where
--     NIZ :: NatIxor ('NS n)
--     NIS :: NatIxor n -> NatIxor ('NS n)

-- emptyUDE :: UDEnv '[]
-- emptyUDE = UDE M.empty ENil

-- nameToEWI :: UDEnv vs -> VName -> Maybe (ExprWIx vs)
-- nameToEWI (UDE mp tv) v = etlToEWI tv <$> M.lookup v mp
--   where
--     etlToEWI :: forall us n. (CompIx us ('NS n) ~ 'LT) => ETList us -> NatIxor n -> ExprWIx us
--     etlToEWI (t :* _)  NIZ      = EWI t (V IZ)
--     etlToEWI (_ :* ts) (NIS ix) = case etlToEWI ts ix of
--                                     EWI t (V ixr) -> EWI t (V (IS ixr))
--                                     _             -> error "i don't know what even"
--     etlToEWI ENil _ = error "type system prevented this"

-- data PolyExpr :: [*] -> * where
--     PE :: Sing n -> (PolyType -> Maybe (VecHole n ETypeW)) -> (Vec n ETypeW -> ExprWIx vs) -> PolyExpr vs

-- -- takes care of the "rest of the m" needed to match the type; you provide
-- -- the n extras.
-- data VecHole :: PNat -> * -> * where
--     VH :: Sing n -> (Vec n a -> Vec m a) -> VecHole m a

-- -- data PolyType :: * where
-- --     PT :: Sing n -> (Vec n ETypeW -> ETypeW) -> PolyType

-- data DumbError = DErrMismatch ETypeW
--                | DErrScope VName
--                | DErrNoUnify ETypeW
--                deriving (Show, Typeable)

-- instance Exception DumbError

-- polyExprNil :: PolyExpr vs -> Maybe (ExprWIx vs)
-- polyExprNil (PE SNZ _ f) = Just $ f VNil
-- polyExprNil _            = Nothing


-- unDumbWith :: forall vs. UDEnv vs -> DumbExpr -> Either DumbError (PolyExpr vs)
-- unDumbWith ude e =
--     case e of
--       DV v -> maybe (throwError (DErrScope v)) return
--             $ PE SNZ (const Nothing) . const <$> nameToEWI ude v
--       DO0 o -> case o of
--                  I _  -> return $ PE SNZ (exactMatch EInt) (\_ -> EWI EInt (O0 o))
--                  B _  -> return $ PE SNZ (exactMatch EBool) (\_ -> EWI EBool (O0 o))
--                  Unit -> return $ PE SNZ (exactMatch EUnit) (\_ -> EWI EUnit (O0 o))
--                  Nil  -> return $ PE (SNS SNZ) (\ts -> do
--                                                   PT SNZ ft <- Just ts
--                                                   ETW (EList t) <- Just $ ft VNil
--                                                   return $ VH SNZ (\_ -> ETW t :> VNil)
--                                                )
--                                                (\(ETW t :> VNil) -> EWI (EList t) (O0 Nil))
--       DO1 o e1 -> case o of
--                     Abs    -> mkO1 o EInt EInt e1
--                     Signum -> mkO1 o EInt EInt e1
--                     Not    -> mkO1 o EBool EBool e1
--                     Left'  -> unDumbLeft e1
--                     Right' -> unDumbRight e1
--                     Fst    -> unDumbFst e1
--                     Snd    -> unDumbSnd e1
--       DO2 o e1 e2 -> case o of
--                        Plus    -> mkO2 o EInt EInt EInt e1 e2
--                        Minus   -> mkO2 o EInt EInt EInt e1 e2
--                        Times   -> mkO2 o EInt EInt EInt e1 e2
--                        LEquals -> mkO2 o EInt EInt EBool e1 e2
--                        And     -> mkO2 o EBool EBool EBool e1 e2
--                        Or      -> mkO2 o EBool EBool EBool e1 e2
--                        Div     -> mkO2 o EInt EInt (EEither EUnit EInt) e1 e2
--                        Mod     -> mkO2 o EInt EInt (EEither EUnit EInt) e1 e2
--                        Tup     -> unDumbTup e1 e2
--                        Cons    -> unDumbCons e1 e2
--                        Ap      -> unDumbAp e1 e2
--       -- DLambda v eλ -> do
--       --     let ude' = case ude of
--       --                  UDE mp vs -> UDE
--     -- UDE :: (CompIx vs ('NS n) ~ 'LT) => Map VName (NatIxor n) -> ETList vs -> UDEnv vs
--           -- eλ <-
--       -- DO3 o e1 e2 e3 -> do
--       --   PE ts1 vh1 f1 <- unDumbWith ude e1
--       --   PE ts2 vh2 f2 <- unDumbWith ude e2
--       --   PE ts3 vh3 f3 <- unDumbWith ude e3
--       --   return $ case o of
--       --              If -> PE (addSN ts1 (addSN ts2 ts3)) (\pt@(PT vts ft) -> do
--       --                                                       undefined
--       --                                                       -- VH hs1 g1 <- vh2 pt
--       --                                                       -- VH hs2 g2 <- vh3 pt
--       --                                                       -- return $ VH (addSN hs1 hs2)
--       --                                                       --             (\etws ->
--       --                                                       --                 let Just etw1 = g1 <$> takeVec hs1 etws
--       --                                                       --                     etw2 = applyOnLast g2 hs1 etws
--       --                                                       --                 in  concatVec etw1 etw2
--       --                                                       --             )
--       --                                                   )
--       --                         undefined
--       --              -- Case -> undefined
--       --              -- UnfoldrN -> undefined
--       --              -- Foldr -> undefined

--   where
--     exactMatch :: EType a -> PolyType -> Maybe (VecHole 'NZ ETypeW)
--     exactMatch t pt = do
--         PT SNZ ft <- Just pt
--         ETW t' <- Just $ ft VNil
--         Ty.Refl <- tyEq t t'
--         return $ VH SNZ (\VNil -> VNil)
--     mkO1 :: Op1 a b
--          -> EType a
--          -> EType b
--          -> DumbExpr
--          -> Either DumbError (PolyExpr vs)
--     mkO1 o t1 t2 e1 = do
--       PE _ vh f <- unDumbWith ude e1
--       VH ts' g <- maybe (throwError (DErrNoUnify (ETW t1))) return
--                 $ vh (PT SNZ (\VNil -> ETW t1))
--       return $ PE ts' (const Nothing) (\xs ->
--                  case f (g xs) of
--                    EWI t1' e1e | Just Ty.Refl <- tyEq t1 t1' -> EWI t2 (O1 o e1e)
--                                | otherwise -> error . unwords $ [ "Lied to by unDumbWith.  Expected "
--                                                                 , show t1
--                                                                 , " but got "
--                                                                 , show t1'
--                                                                 ]
--                )
--     mkO2 :: Op2 a b c
--          -> EType a
--          -> EType b
--          -> EType c
--          -> DumbExpr
--          -> DumbExpr
--          -> Either DumbError (PolyExpr vs)
--     mkO2 o t1 t2 t3 e1 e2 = do
--       PE _ vh1 f1 <- unDumbWith ude e1
--       PE _ vh2 f2 <- unDumbWith ude e2
--       VH ts1' g1 <- maybe (throwError (DErrNoUnify (ETW t1))) return
--                   $ vh1 (PT SNZ (\VNil -> ETW t1))
--       VH ts2' g2 <- maybe (throwError (DErrNoUnify (ETW t2))) return
--                   $ vh2 (PT SNZ (\VNil -> ETW t2))
--       return $ PE (addSN ts1' ts2') (const Nothing) (\xs ->
--                     let Just ew1 = f1 . g1 <$> takeVec ts1' xs
--                         ew2      = applyOnLast (f2 . g2) ts1' xs
--                     in  case (ew1, ew2) of
--                           (EWI t1' e1e, EWI t2' e2e) | Just Ty.Refl <- tyEq t1 t1'
--                                                      , Just Ty.Refl <- tyEq t2 t2'
--                                                      -> EWI t3 (O2 o e1e e2e)
--                                                      | otherwise
--                                                      -> error . unwords $ [ "Lied to by unDumbWith.  Expected "
--                                                                           , show t1 ++ " and " ++ show t2
--                                                                           , " but got "
--                                                                           , show t1' ++ " and " ++ show t2'
--                                                                           ]
--                   )
--     unDumbLeft :: DumbExpr -> Either DumbError (PolyExpr vs)
--     unDumbLeft e1 = do
--       PE ts vh f <- unDumbWith ude e1
--       return $ PE (SNS ts) (\pt -> do
--                                PT SNZ ft <- Just pt
--                                ETW (EEither t1 t2) <- Just $ ft VNil        -- most likely wrong!!!!! can be poly/scheme
--                                VH hs g <- vh $ PT SNZ (\VNil -> ETW t1)     -- get the inner to be the expected input
--                                return $ VH hs (\xs -> ETW t2 :> g xs)
--                   )
--                   (\(ETW t :> etws) -> case f etws of
--                                          EWI e1t e1e -> EWI (EEither e1t t) (O1 Left' e1e)
--                   )
--     unDumbRight :: DumbExpr -> Either DumbError (PolyExpr vs)
--     unDumbRight e1 = do
--       PE ts vh f <- unDumbWith ude e1
--       return $ PE (SNS ts) (\pt -> do
--                                PT SNZ ft <- Just pt
--                                ETW (EEither t1 t2) <- Just $ ft VNil
--                                VH hs g <- vh $ PT SNZ (\VNil -> ETW t2)
--                                return $ VH hs (\xs -> ETW t1 :> g xs)
--                   )
--                   (\(ETW t :> etws) -> case f etws of
--                                          EWI e1t e1e -> EWI (EEither t e1t) (O1 Right' e1e)
--                   )
--     unDumbFst :: DumbExpr -> Either DumbError (PolyExpr vs)
--     unDumbFst e1 = do
--       PE ts vh f <- unDumbWith ude e1
--       return $ PE ts (\(PT vts ft) ->
--                          vh $ PT (SNS vts) (\(ETW u :> us) ->
--                            case ft us of
--                              ETW t1 -> ETW (ETup t1 u)
--                          )
--                      )
--                      (\etws -> case f etws of
--                                  EWI (ETup e1t _) e1e -> EWI e1t (O1 Fst e1e)
--                                  _                    -> error "unDumbWith lie"
--                                      )
--     unDumbSnd :: DumbExpr -> Either DumbError (PolyExpr vs)
--     unDumbSnd e1 = do
--       PE ts vh f <- unDumbWith ude e1
--       return $ PE ts (\(PT vts ft) ->
--                          vh $ PT (SNS vts) (\(ETW u :> us) ->
--                            case ft us of
--                              ETW t1 -> ETW (ETup u t1)
--                          )
--                      )
--                      (\etws -> case f etws of
--                                  EWI (ETup _ e1t) e1e -> EWI e1t (O1 Snd e1e)
--                                  _                    -> error "unDumbWith lie"
--                      )
--     unDumbTup :: DumbExpr -> DumbExpr -> Either DumbError (PolyExpr vs)
--     unDumbTup e1 e2 = do
--       PE ts1 vh1 f1 <- unDumbWith ude e1
--       PE ts2 vh2 f2 <- unDumbWith ude e2
--       return $ PE (addSN ts1 ts2) (\pt -> do
--                                     PT SNZ ft <- Just pt
--                                     ETW (ETup t1 t2) <- Just $ ft VNil
--                                     VH hs1 g1 <- vh1 $ PT SNZ (\VNil -> ETW t1)
--                                     VH hs2 g2 <- vh2 $ PT SNZ (\VNil -> ETW t2)
--                                     return $ VH (addSN hs1 hs2)
--                                                 (\etws -> let Just etw1 = g1 <$> takeVec hs1 etws
--                                                               etw2 = applyOnLast g2 hs1 etws
--                                                           in  concatVec etw1 etw2
--                                                 )
--                                   )
--                                   (\etws -> let Just ew1 = f1 <$> takeVec ts1 etws
--                                                 ew2      = applyOnLast f2 ts1 etws
--                                             in  case (ew1, ew2) of
--                                                   (EWI t1 e1e, EWI t2 e2e) ->
--                                                     EWI (ETup t1 t2) (O2 Tup e1e e2e)
--                                   )
--     unDumbCons :: DumbExpr -> DumbExpr -> Either DumbError (PolyExpr vs)
--     unDumbCons e1 e2 = do
--       PE ts1 vh1 f1 <- unDumbWith ude e1
--       PE ts2 vh2 f2 <- unDumbWith ude e2
--       return $ PE (addSN ts1 ts2) (\pt -> do
--                                      PT SNZ ft <- Just pt
--                                      ETW (EList t) <- Just $ ft VNil
--                                      VH hs1 g1 <- vh1 $ PT SNZ (\VNil -> ETW t)
--                                      VH hs2 g2 <- vh2 $ PT SNZ (\VNil -> ETW (EList t))
--                                      return $ VH (addSN hs1 hs2)
--                                                  (\etws -> let Just etw1 = g1 <$> takeVec hs1 etws
--                                                                etw2 = applyOnLast g2 hs1 etws
--                                                            in  concatVec etw1 etw2
--                                                  )
--                                   )
--                                   (\etws -> let Just ew1 = f1 <$> takeVec ts1 etws
--                                                 ew2      = applyOnLast f2 ts1 etws
--                                             in  case (ew1, ew2) of
--                                                   (EWI t1 e1e, EWI (EList t1') e2e)
--                                                     | Just Ty.Refl <- tyEq t1 t1'
--                                                     -> EWI (EList t1) (O2 Cons e1e e2e)
--                                                   _ -> error "hey, does this work?"
--                                   )
--     unDumbAp :: DumbExpr -> DumbExpr -> Either DumbError (PolyExpr vs)
--     unDumbAp e1 e2 = do
--       PE ts1 vh1 f1 <- unDumbWith ude e1
--       PE ts2 vh2 f2 <- unDumbWith ude e2
--       return $ PE (addSN ts1 ts2)
--                   (\(PT vts ft) -> do
--         -- feed g1 a vec and give the result to f1 and get something that
--         -- can tell the type of PE?
--         -- but how to get vec..? maybe only be happy if g1 expects SNZ?
--         -- does this workkkkk????? will this ever not be SNZ?  need to do
--         -- lambda before testing.
--         VH SNZ g1 <- vh1 $ PT (SNS vts) (\(ETW u :> us) ->
--                                              case ft us of
--                                                ETW t -> ETW (EFunc u t)
--                                         )
--         EWI (EFunc t0 _) _ <- Just $ f1 (g1 VNil)
--         VH hs2 g2 <- vh2 $ PT vts (\_ -> ETW t0)
--         return $ VH hs2
--                     (\etws -> let Just etw1 = g1 <$> takeVec SNZ etws
--                                   etw2      = applyOnLast g2 SNZ etws
--                               in  concatVec etw1 etw2
--                     )
--                   )
--                   (\etws -> let Just ew1 = f1 <$> takeVec ts1 etws
--                                 ew2      = applyOnLast f2 ts1 etws
--                             in  case (ew1, ew2) of
--                                   (EWI (EFunc t1 t2) e1e, EWI t1' e2e)
--                                     | Just Ty.Refl <- tyEq t1 t1'
--                                     -> EWI t2 (O2 Ap e1e e2e)
--                                   _ -> error "hey what is going on, is this possible?"
--                                   -- actually, might be very possible.
--                                   -- because type checking is deffered
--                                   -- until here.  should be some way to
--                                   -- make sure that this works no matter
--                                   -- what...
--                   )
