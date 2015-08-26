{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DataKinds #-}

module Data.ExprGADT.Generate where

import Control.Monad.Random
import Debug.Trace
import Control.Applicative
import Data.ExprGADT.Types
import Data.ExprGADT.Expr
import Data.ExprGADT.Eval
import Data.Bifunctor
import Data.ExprGADT.Traversals
import Control.Monad

data Chain :: (* -> *) -> * -> * -> * where
    CLeaf :: p (a -> b) -> Chain p a b
    CNode :: Chain p a b -> Chain p b c -> Chain p a c

type EChain = Chain EType

type ExprGenerator m vs a = Int -> m (Expr vs a)

type ExprGenerators m vs a = Int -> [(m (Expr vs a), Rational)]

genFromEType :: MonadRandom m => EType a -> ExprGenerator m vs a
genFromEType e = join . fromList . etGenerators e

etGenerators :: forall m vs a. MonadRandom m => EType a -> ExprGenerators m vs a
etGenerators t = do
    d <- id
    let pGens :: MonadRandom m => ExprGenerators m vs a
        pGens | d > 0     = polyGenerators t
              | otherwise = return []
    case t of
      EInt          -> concat <$> sequence [intGenerators, pGens]
      EBool         -> concat <$> sequence [boolGenerators, pGens]
      EUnit         -> concat <$> sequence [unitGenerators]
      EList t1      -> concat <$> sequence [listGenerators t1, pGens]
      ETup t1 t2    -> concat <$> sequence [tupleGenerators t1 t2, pGens]
      EEither t1 t2 -> concat <$> sequence [eitherGenerators t1 t2, pGens]
      EFunc t1 t2 | d <= 0   -> (:[]) . (,1) <$> generateConst t2
                  | eTypeDepth t1 > 1 || eTypeDepth t2 > 1 -> (:[]) . (,1) <$> generateConst t2
      EFunc EInt a          -> (map . first) toIntFunction <$> etGenerators a
      EFunc EBool a         -> (map . first) toBoolFunction <$> etGenerators a
      EFunc EUnit a         -> (map . first) toUnitFunction <$> etGenerators a
      EFunc (ETup a b) c    -> (map . first . fmap) uncurry' <$> etGenerators (EFunc a (EFunc b c))
      EFunc (EEither a b) c -> liftA2 (\(f,x) (g,y) -> (caseUp f g, x+y)) <$> etGenerators (EFunc a c) <*> etGenerators (EFunc b c)
      EFunc (EList x) y     -> case y of
                                 EList z -> (:) <$> fmap (,1) (ana x y)
                                                <*> listFuncGenerators x z
                                 _ -> (:[]) . (,1) <$> ana x y
      EFunc (EFunc x y) z   -> (:[]) . (,1) <$> funcFuncGen x y z
  where
    p :: Double
    p = 0.5
    generateConst :: forall b c us. EType c -> ExprGenerator m us (b -> c)
    generateConst t1 d = do
        e <- overIxors IS <$> genFromEType t1 (d - 1)
        return $ λ .-> e
    toIntFunction :: forall b us. m (Expr us b) -> m (Expr us (Int -> b))
    toIntFunction gx = do
        e  <- overIxors IS <$> gx
        e' <- flip traverseIntLeaves e $ \i -> do
                c <- (<= p) <$> getRandomR (0, 1)
                return $ if c then V IZ else iI i
        return $ λ .-> e'
    toBoolFunction :: forall b us. m (Expr us b) -> m (Expr us (Bool -> b))
    toBoolFunction gx = do
        e  <- overIxors IS <$> gx
        e' <- flip traverseBoolLeaves e $ \b -> do
                c <- (<= p) <$> getRandomR (0, 1)
                return $ if c then V IZ else bB b
        return $ λ .-> e'
    toUnitFunction :: forall b us. m (Expr us b) -> m (Expr us (() -> b))
    toUnitFunction gx = do
      e <- pushInto <$> gx
      return $ λ .-> e
    caseUp :: forall us b c d.
              m (Expr (Either b c ': us) (b -> d))
           -> m (Expr (Either b c ': us) (c -> d))
           -> m (Expr us (Either b c -> d))
    caseUp gx gy = do
      ef <- gx
      eg <- gy
      return $ λ .-> case' (V IZ) ef eg
    ana :: forall us b c. EType b -> EType c -> ExprGenerator m us ([b] -> c)
    ana t1 t2 d = do
      f <- genFromEType (EFunc t1 (EFunc t2 t2)) (d - 1)
      z <- genFromEType t2 (d - 1)
      return $ λ .-> foldr' f z (V IZ)
    funcFuncGen :: forall us b c d. EType b -> EType c -> EType d -> ExprGenerator m us ((b -> c) -> d)
    funcFuncGen t1 t2 t3 d = do
      z <- genFromEType t1 (d - 1)
      f <- genFromEType (EFunc t2 t3) (d - 1)
      return $ λ .-> f ~$ (V IZ ~$ z)


polyGenerators :: MonadRandom m => EType a -> ExprGenerators m vs a
polyGenerators t d = (map . second) (/4) gens
  where
    gens = [ (generateFst, 0.5 * polyWeight)
           , (generateSnd, 0.5 * polyWeight)
           , (generateAp, polyWeight)
           , (if' <$> generateBool <*> generateX <*> generateX , 1)
           , (generateCase, polyWeight)
           , (generateFold, polyWeight)
           ]
    polyWeight | eTypeDepth t > 1 = 0
               | otherwise        = 1
    generateBool = genFromEType EBool (d - 1)
    generateX    = genFromEType t (d - 1)
    generateFst = do
      ETW t1 <- generateETypeW $ min typeDepth (d - 1)
      et <- genFromEType (ETup t t1) (d `div` 2)
      return $ fst' et
    generateSnd = do
      ETW t1 <- generateETypeW $ min typeDepth (d - 1)
      et <- genFromEType (ETup t1 t) (d `div` 2)
      return $ snd' et
    generateCase = do
      ETW t1 <- generateETypeW $ min typeDepth (d - 1)
      ETW t2 <- generateETypeW $ min typeDepth (d - 1)
      ee <- genFromEType (EEither t1 t2) (d - 1)
      el <- genFromEType (EFunc t1 t) (d - 1)
      er <- genFromEType (EFunc t2 t) (d - 1)
      return $ case' ee el er
    generateAp = do
      ETW t1 <- generateETypeW $ min typeDepth (d - 1)
      ef <- genFromEType (EFunc t1 t) (d - 1)
      ex <- genFromEType t1 (d - 1)
      return $ ef ~$ ex
    generateFold = do
      ETW t1 <- generateETypeW $ min typeDepth (d - 1)
      -- infinite loop happens in generating ef
      ef <- genFromEType (EFunc t1 (EFunc t t)) (d - 1)
      ez <- genFromEType t (d - 1)
      exs <- genFromEType (EList t1) (d - 1)
      return $ foldr' ef ez exs

generateETypeW :: MonadRandom m => Int -> m ETypeW
generateETypeW d | d <= 0    = join (fromList gens0)
                 | otherwise = join (fromList gens)
  where
    gens0 = [ (return (ETW EInt) , 1)
            , (return (ETW EBool), 1)
            , (return (ETW EUnit), 1)
            ]
    gens  = gens0
         ++ [ ((\(ETW t1) (ETW t2) -> ETW (ETup t1 t2)) <$> generateETypeW' <*> generateETypeW'    , 0.5)
            , ((\(ETW t1) (ETW t2) -> ETW (EEither t1 t2)) <$> generateETypeW' <*> generateETypeW' , 0.5)
            , ((\(ETW t1) (ETW t2) -> ETW (EFunc t1 t2)) <$> generateETypeW' <*> generateETypeW'   , 0.25)
            , ((\(ETW t) -> ETW (EList t)) <$> generateETypeW'                                     , 0.5)
            ]
    generateETypeW' = generateETypeW (d - 1)


intGenerators :: MonadRandom m => ExprGenerators m vs Int
intGenerators d = (iI <$> getRandomR (-20, 20), 1)
                : if d > 0 then gens else []
  where
    gens = [ (abs <$> generateInt                                , 1)
           , (signum <$> generateInt                             , 1)
           , ((+) <$> generateInt <*> generateInt                , 1)
           , ((*) <$> generateInt <*> generateInt                , 1)
           , ((-) <$> generateInt <*> generateInt                , 1)
           ]
    generateInt = genFromEType EInt (d - 1)

boolGenerators :: MonadRandom m => ExprGenerators m vs Bool
boolGenerators d = (bB <$> getRandom, 1)
                 : if d > 0 then gens else []
  where
    gens = [ (not' <$> generateBool                              , 1)
           , ((~<=) <$> generateInt <*> generateInt              , 1)
           , ((~<) <$> generateInt <*> generateInt               , 1)
           , ((~==) <$> generateInt <*> generateInt              , 1)
           , (divides' <$> generateInt <*> generateInt           , 1)
           , ((~&&) <$> generateBool <*> generateBool            , 1)
           , ((~||) <$> generateBool <*> generateBool            , 1)
           , (xor' <$> generateBool <*> generateBool             , 1)
           ]
    generateBool = genFromEType EBool (d - 1)
    generateInt  = genFromEType EInt (d - 1)

-- -- this is kind of silly, heh
unitGenerators :: MonadRandom m => ExprGenerators m vs ()
unitGenerators d = (return unit', 1)
                 : if d > 0 then gens else []
  where
    gens = []

listGenerators :: MonadRandom m => EType a -> ExprGenerators m vs [a]
listGenerators t d = (return nil', 0.1)
                   : if d > 0 then gens else []
  where
    gens = [ ((~:) <$> generateX <*> generateList       , 1)
           , (generateMap                               , polyWeight)
           , (generateMapMaybe                          , polyWeight)
           , (filter' <$> generatePred <*> generateList , 1)
           , ((~++) <$> generateList <*> generateList   , 1)
           , (take' <$> generateInt <*> generateList    , 1)
           , (generateUnfoldrN                          , polyWeight)
           , (generateUnfoldrNUntil                     , polyWeight)
           ]
    polyWeight | eTypeDepth t > 1 = 0
               | otherwise        = 1
    generateX    = genFromEType t (d - 1)
    generateList = genFromEType (EList t) (d - 1)
    generateInt  = min' 50 . abs <$> genFromEType EInt (d - 1)
    generateInt' = min' (iI (d * 2)) <$> generateInt
    generatePred = genFromEType (EFunc t EBool) (d - 1)
    generateMap = do
      ETW t1 <- generateETypeW $ min typeDepth (d - 1)
      f <- genFromEType (EFunc t1 t) (d - 1)
      xs <- genFromEType (EList t1) (d - 1)
      return $ map' f xs
    generateMapMaybe = do
      ETW t1 <- generateETypeW $ min typeDepth (d - 1)
      f <- genFromEType (EFunc t1 (EEither EUnit t)) (d - 1)
      xs <- genFromEType (EList t1) (d - 1)
      return $ mapMaybe' f xs
    generateUnfoldrN = do
      ETW t1 <- generateETypeW $ min typeDepth (d - 1)
      n <- generateInt'
      f <- genFromEType (EFunc t1 (ETup t t1)) (d - 1)
      z <- genFromEType t1 (d - 1)
      return $ unfoldrN' n f z
    generateUnfoldrNUntil = do
      ETW t1 <- generateETypeW $ min typeDepth (d - 1)
      n <- generateInt'
      f <- genFromEType (EFunc t1 (EEither EUnit (ETup t t1))) (d - 1)
      z <- genFromEType t1 (d - 1)
      return $ unfoldrNUntil' n f z

typeDepth :: Int
typeDepth = 1

tupleGenerators :: MonadRandom m => EType a -> EType b -> ExprGenerators m vs (a, b)
tupleGenerators t1 t2 d = gens
  where
    gens = [ (tup' <$> generateX <*> generateY, 1) ]
    generateX = genFromEType t1 (d - 1)
    generateY = genFromEType t2 (d - 1)

eitherGenerators :: forall m vs a b. MonadRandom m => EType a -> EType b -> ExprGenerators m vs (Either a b)
eitherGenerators t1 t2 d = gens
                        ++ case (t1, t2) of
                             (EUnit, EInt) -> gensInt
                             _             -> []
  where
    gens = [ (left' <$> generateX , 1)
           , (right' <$> generateY, 1)
           ]
    gensInt :: [(m (Expr vs (Maybe' Int)), Rational)]
    gensInt = [ (div' <$> generateInt <*> generateInt, 1 )
              , (mod' <$> generateInt <*> generateInt, 1 )
              ]
    generateInt = genFromEType EInt (d - 1)
    generateX   = genFromEType t1 (d - 1)
    generateY   = genFromEType t2 (d - 1)

listFuncGenerators :: forall m vs a b. MonadRandom m => EType a -> EType b -> ExprGenerators m vs ([a] -> [b])
listFuncGenerators t1 t2 d = gens
  where
    gens = [ ((\f g -> λ .-> filter' f (map' g (V IZ))) <$> generatePredY <*> generateMapper, 1)
           , ((\f g -> λ .-> map' f (filter' g (V IZ))) <$> generateMapper <*> generatePredX, 1)
           , (λ . flip mapMaybe' (V IZ) <$> generateMaybe, polyWeight)
           , ((\i f -> λ .-> take' i (map' f (V IZ))) <$> generateInt <*> generateMapper, 1)
           , ((\ys f -> λ .-> map' f (V IZ) ~++ ys) <$> generateListY <*> generateMapper, 0.5)
           , ((\ys f -> λ .-> ys ~++ map' f (V IZ)) <$> generateListY <*> generateMapper, 0.5)
           , ((\xs f -> λ .-> map' f (V IZ ~++ xs)) <$> generateListX <*> generateMapper, 0.5)
           , ((\xs f -> λ .-> map' f (xs ~++ V IZ)) <$> generateListX <*> generateMapper, 0.5)
           ]
    polyWeight | eTypeDepth t1 > 1 = 0
               | eTypeDepth t2 > 1 = 0
               | otherwise         = 2
    generateInt :: forall us. m  (Expr us Int)
    generateInt = min' 50 . abs <$> genFromEType EInt (d - 1)
    generateMapper :: forall us. m (Expr us (a -> b))
    generateMapper = genFromEType (EFunc t1 t2) (d - 1)
    generatePredX :: forall us. m (Expr us (a -> Bool))
    generatePredX = genFromEType (EFunc t1 EBool) (d - 1)
    generatePredY :: forall us. m (Expr us (b -> Bool))
    generatePredY = genFromEType (EFunc t2 EBool) (d - 1)
    generateMaybe :: forall us. m (Expr us (a -> Maybe' b))
    generateMaybe = genFromEType (EFunc t1 (EEither EUnit t2)) (d - 1)
    generateListX :: forall us. m (Expr us [a])
    generateListX = genFromEType (EList t1) (d - 1)
    generateListY :: forall us. m (Expr us [b])
    generateListY = genFromEType (EList t2) (d - 1)
