{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}

module Data.ExprGADT.Dumb where

-- import Data.ExprGADT.Dumb.Infer
import Data.ExprGADT.Dumb.Types
import Data.ExprGADT.Types
import Data.ExprGADT.Traversals
import Data.Map.Strict           (Map)
import Data.Proxy
import Control.Monad.Except
import Data.Singletons
import Unsafe.Coerce
import Data.Maybe
import qualified Data.Map.Strict as M

data PolyType :: * where
    PT :: Sing n -> (Vec n ETypeW -> ETypeW) -> PolyType

data PNat :: * where
    NZ :: PNat
    NS :: PNat -> PNat
  deriving (Eq, Ord, Show)

data instance Sing (n :: PNat) where
    SNZ :: Sing 'NZ
    SNS :: Sing (m :: PNat) -> Sing ('NS m)

data Vec :: PNat -> * -> * where
    VNil :: Vec 'NZ a
    (:>) :: a -> Vec n a -> Vec ('NS n) a

infixr 5 :>

instance Functor (Vec n) where
    fmap _ VNil = VNil
    fmap f (x :> xs) = f x :> fmap f xs

instance Applicative (Vec 'NZ) where
    pure _ = VNil
    _ <*> _ = VNil

instance Applicative (Vec n) => Applicative (Vec ('NS n)) where
    pure x = x :> pure x
    (f :> fx) <*> (x :> xs) = f x :> (fx <*> xs)

type family NPlus (n :: PNat) (m :: PNat) :: PNat where
    NPlus 'NZ m = m
    NPlus ('NS n) m = 'NS (NPlus n m)

addSN :: forall n m nm. (NPlus n m ~ nm)
      => Sing n -> Sing m -> Sing nm
addSN SNZ y = y
addSN (SNS x) y = SNS (addSN x y)

type family NSub (n :: PNat) (m :: PNat) :: PNat where
    NSub n      'NZ      = 'NZ
    NSub 'NZ     m       = m
    NSub ('NS n) ('NS m)  = NSub n m

subSN :: forall n m nm. (NSub n m ~ nm)
      => Sing n -> Sing m -> Sing nm
subSN _ SNZ = SNZ
subSN SNZ y = y
subSN (SNS x) (SNS y) = subSN x y

type family NComp (n :: PNat) (m :: PNat) :: Ordering where
    NComp 'NZ 'NZ = 'EQ
    NComp n 'NZ = 'GT
    NComp 'NZ m = 'LT
    NComp ('NS n) ('NS m) = NComp n m

type family NMin (n :: PNat) (m :: PNat) :: PNat where
    NMin n 'NZ = 'NZ
    NMin 'NZ m = 'NZ
    NMin ('NS n) ('NS m) = 'NS (NMin n m)

instance SingI 'NZ where
    sing = SNZ

instance SingI n => SingI ('NS n) where
    sing = SNS sing

takeVec :: Sing n -> Vec m a -> Maybe (Vec n a)
takeVec SNZ _             = Just VNil
takeVec (SNS n) (x :> xs) = (x :>) <$> takeVec n xs
takeVec (SNS _) VNil      = Nothing

applyOnLast :: (Vec m a -> b) -> Sing n -> Vec (NPlus n m) a -> b
applyOnLast f SNZ xs = f xs
applyOnLast f (SNS i) (_ :> xs) = applyOnLast f i xs
applyOnLast _ (SNS _) _ = error "impossible...cannot be called."

collapseTExpr :: TExpr -> PolyType
collapseTExpr (TEV _)  = PT (SNS SNZ) (\(t :> VNil) -> t)    -- todo
collapseTExpr (TEO0 t) = PT SNZ (\_ -> ETW t)
collapseTExpr (TEO1 o t1) = case collapseTExpr t1 of
                              PT n f ->
                                case o of
                                  TOList -> PT n $ \ts ->
                                              case f ts of
                                                ETW t -> ETW (EList t)
collapseTExpr (TEO2 o t1 t2) = case (collapseTExpr t1, collapseTExpr t2) of
                                 (PT (n :: Sing n) f, PT (m :: Sing m) g) ->
                                   PT (addSN n m) $ \(ts :: Vec (NPlus n m) ETypeW) ->
                                     let Just etw1 = f <$> takeVec n ts
                                         etw2 = applyOnLast g n ts
                                     in  case (etw1, etw2) of
                                           (ETW t1', ETW t2') -> case o of
                                                                   TOEither -> ETW (EEither t1' t2')
                                                                   TOTuple -> ETW (ETup t1' t2')
                                                                   TOFunc -> ETW (EFunc t1' t2')

type family CompIx (as :: [k]) (n :: PNat) :: Ordering where
    CompIx '[] 'NZ = 'EQ
    CompIx '[] x   = 'LT
    CompIx xs  'NZ = 'GT
    CompIx (x ': xs) ('NS i) = CompIx xs i

data UDEnv :: [*] -> * where
    UDE :: (CompIx vs ('NS n) ~ 'LT) => Map VName (NatIxor n) -> ETList vs -> UDEnv vs

data NatIxor :: PNat -> * where
    NIZ :: NatIxor ('NS n)
    NIS :: NatIxor n -> NatIxor ('NS n)

emptyUDE :: UDEnv '[]
emptyUDE = UDE M.empty ENil

nameToEWI :: UDEnv vs -> VName -> Maybe (ExprWIx vs)
nameToEWI (UDE mp tv) v = etlToEWI tv <$> M.lookup v mp
  where
    etlToEWI :: forall us n. (CompIx us ('NS n) ~ 'LT) => ETList us -> NatIxor n -> ExprWIx us
    etlToEWI (t :* _)  NIZ      = EWI t (V IZ)
    etlToEWI (_ :* ts) (NIS ix) = case etlToEWI ts ix of
                                    EWI t (V ixr) -> EWI t (V (IS ixr))
                                    _             -> error "i don't know what even"
    etlToEWI ENil _ = error "type system prevented this"

data PolyExpr :: [*] -> * where
    PE :: Sing n -> (PolyType -> Maybe (VecHole n ETypeW)) -> (Vec n ETypeW -> ExprWIx vs) -> PolyExpr vs

data VecHole :: PNat -> * -> * where
    VH :: Sing n -> (Vec n a -> Vec m a) -> VecHole m a

-- data PolyType :: * where
--     PT :: Sing n -> (Vec n ETypeW -> ETypeW) -> PolyType

data DumbError = DErrMismatch ETypeW
               | DErrScope VName
               | DErrNoUnify ETypeW

unDumbWith :: forall vs. UDEnv vs -> DumbExpr -> Either DumbError (PolyExpr vs)
unDumbWith ude e =
    case e of
      DV v -> maybe (throwError (DErrScope v)) return
            $ PE SNZ (const Nothing) . const <$> nameToEWI ude v
      DO0 o -> case o of
                 I _  -> return . PE SNZ (const Nothing) $ \_ -> EWI EInt (O0 o)
                 B _  -> return . PE SNZ (const Nothing) $ \_ -> EWI EBool (O0 o)
                 Unit -> return . PE SNZ (const Nothing) $ \_ -> EWI EUnit (O0 o)
                 Nil  -> return $ PE (SNS SNZ) (\ts -> do
                                                  PT SNZ ft <- Just ts
                                                  ETW (EList t) <- Just $ ft VNil
                                                  return $ VH SNZ (\_ -> ETW t :> VNil)
                                               )
                                               (\(ETW t :> VNil) -> EWI (EList t) (O0 Nil))
      DO1 o e1 -> case o of
                    Abs    -> mkO1 EInt  e1 $ \case EWI EInt  e1e -> Just $ EWI EInt (O1 o e1e)
                                                    _             -> Nothing
                    Signum -> mkO1 EInt  e1 $ \case EWI EInt  e1e -> Just $ EWI EInt (O1 o e1e)
                                                    _             -> Nothing
                    Not    -> mkO1 EBool e1 $ \case EWI EBool e1e -> Just $ EWI EBool (O1 o e1e)
                                                    _             -> Nothing
                    Left'  -> do
                      PE ts vh f <- unDumbWith ude e1
                      return $ PE (SNS ts) (\ts -> do
                                               PT SNZ ft <- Just ts
                                               ETW (EEither t1 t2) <- Just $ ft VNil
                                               VH hs g <- vh $ PT SNZ (\VNil -> ETW t1)     -- get the inner to be the expected input
                                               return $ VH hs (\xs -> ETW t2 :> g xs)
                                  )
                                  (\(ETW t :> etws) -> case f etws of
                                                         EWI e1t e1e -> EWI (EEither e1t t) (O1 Left' e1e)
                                  )
                    Right' -> do
                      PE ts vh f <- unDumbWith ude e1
                      return $ PE (SNS ts) (\ts -> do
                                               PT SNZ ft <- Just ts
                                               ETW (EEither t1 t2) <- Just $ ft VNil
                                               VH hs g <- vh $ PT SNZ (\VNil -> ETW t2)
                                               return $ VH hs (\xs -> ETW t1 :> g xs)
                                  )
                                  (\(ETW t :> etws) -> case f etws of
                                                         EWI e1t e1e -> EWI (EEither t e1t) (O1 Right' e1e)
                                  )
                    Fst -> do
                      PE ts vh f <- unDumbWith ude e1
                      return $ PE ts (\(PT vts ft) ->
                                         vh $ PT (SNS vts) (\(ETW u :> us) ->
                                           case ft us of
                                             ETW t1 -> ETW (ETup t1 u)
                                         )
                                     )
                                     (\etws -> case f etws of
                                                 EWI (ETup e1t _) e1e -> EWI e1t (O1 Fst e1e)
                                                 _                    -> error "unDumbWith lie"
                                     )
                    Snd -> do
                      PE ts vh f <- unDumbWith ude e1
                      return $ PE ts (\(PT vts ft) ->
                                         vh $ PT (SNS vts) (\(ETW u :> us) ->
                                           case ft us of
                                             ETW t1 -> ETW (ETup u t1)
                                         )
                                     )
                                     (\etws -> case f etws of
                                                 EWI (ETup _ e1t) e1e -> EWI e1t (O1 Snd e1e)
                                                 _                    -> error "unDumbWith lie"
                                     )

  where
    mkO1 :: EType a -> DumbExpr -> (ExprWIx vs -> Maybe (ExprWIx vs)) -> Either DumbError (PolyExpr vs)
    mkO1 t1 e1 apply = do
      PE ts vh f <- unDumbWith ude e1
      VH ts' g <- maybe (throwError (DErrNoUnify (ETW t1))) return
                $ vh (PT SNZ (\VNil -> ETW t1))
      return $ PE ts' (const Nothing) (\xs ->
                 let ew = f (g xs)
                     err = case ew of
                             EWI t0 _ -> error . unwords $ [ "Lied to by unDumbWith.  Expected "
                                                           , show t1
                                                           , " but got "
                                                           , show t0
                                                           ]
                 in  fromMaybe err (apply ew)
               )

--       DO2 o e1 e2 -> case o of
--                        Plus -> mkO2 EInt EInt e1 e2 $ \ew1 ew2 ->
--                                  case (ew1, ew2) of
--                                    (EW e1vs EInt e1e, EW e2vs EInt e2e) ->
--                                      Just $ EW undefined EInt undefined
--                                    _ -> Nothing
--   where
--     mkO1 :: EType a -> DumbExpr -> (ExprW -> Maybe ExprW) -> Maybe PolyExpr
--     mkO1 t1 e1 apply = do
--       PE ts vh f <- unDumbWith ude e1
--       VH ts' g <- vh $ PT SNZ (\VNil -> ETW t1)
--       return $ PE ts' (const Nothing) (\xs ->
--                  let ew = f (g xs)
--                      err = case ew of
--                              EW _ t0 _ -> error . unwords $ [ "Lied to by unDumbWith.  Expected "
--                                                             , show t1
--                                                             , " but got "
--                                                             , show t0
--                                                             ]
--                  in  fromMaybe err (apply ew)
--                )
--     mkO2 :: EType a -> EType b -> DumbExpr -> DumbExpr -> (ExprW -> ExprW -> Maybe ExprW) -> Maybe PolyExpr
--     mkO2 t1 t2 e1 e2 apply = do
--       PE ts1 vh1 f1 <- unDumbWith ude e1
--       PE ts2 vh2 f2 <- unDumbWith ude e2
--       VH ts1' g1 <- vh1 $ PT SNZ (\VNil -> ETW t1)
--       VH ts2' g2 <- vh2 $ PT SNZ (\VNil -> ETW t2)
--       return $ PE (addSN ts1' ts2') (const Nothing) (\xs ->
--                     let Just ew1 = f1 . g1 <$> takeVec ts1' xs
--                         ew2      = applyOnLast (f2 . g2) ts1' xs
--                         err      = case (ew1, ew2) of
--                                        (EW _ t1' _, EW _ t2' _) ->
--                                          error . unwords $ [ "Lied to by unDumbWith.  Expected "
--                                                            , show t1 ++ " and " ++ show t2
--                                                            , " but got "
--                                                            , show t1' ++ " and " ++ show t2'
--                                                            ]
--                     in  fromJust (apply ew1 ew2)
--                   )
--       -- undefined
-- -- collapseTExpr (TEO2 o t1 t2) = case (collapseTExpr t1, collapseTExpr t2) of
-- --                                  (PT (n :: Sing n) f, PT (m :: Sing m) g) ->
-- --                                    PT (addSN n m) $ \(ts :: Vec (NPlus n m) ETypeW) ->
-- --                                      let Just etw1 = f <$> takeVec n ts
-- --                                          etw2 = applyOnLast g n ts
-- --                                      in  case (etw1, etw2) of
-- --                                            (ETW t1', ETW t2') -> case o of
-- --                                                                    TOEither -> ETW (EEither t1' t2')
-- --                                                                    TOTuple -> ETW (ETup t1' t2')
-- --                                                                    TOFunc -> ETW (EFunc t1' t2')
