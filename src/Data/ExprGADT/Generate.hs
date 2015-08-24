{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.ExprGADT.Generate where

import Control.Monad.Random
import Data.ExprGADT.Types
import Data.ExprGADT.Expr
import Control.Monad

type ExprGenerator m vs a = Int -> m (Expr vs a)

generateIf :: MonadRandom m => ExprGenerator m vs a -> ExprGenerator m vs a
generateIf gx d = if' <$> generateBool (d - 1) <*> gx (d - 1) <*> gx (d - 1)

generateInt :: MonadRandom m => ExprGenerator m vs Int
generateInt d | d <= 0    = iI <$> getRandomR (-20,20)
              | otherwise = join (fromList gens)
  where
    gens = [ (iI <$> getRandomR (-20, 29)                          , 1)
           , (abs <$> generateInt'                                 , 1)
           , (signum <$> generateInt'                              , 1)
           , (fst' <$> undefined                                   , 0)
           , (snd' <$> undefined                                   , 0)
           , ((+) <$> generateInt' <*> generateInt'                , 1)
           , ((*) <$> generateInt' <*> generateInt'                , 1)
           , ((-) <$> generateInt' <*> generateInt'                , 1)
           , ((~$) <$> undefined <*> undefined                     , 0)
           , (generateIf generateInt d                             , 1)
           , (case' <$> undefined <*> undefined <*> undefined      , 0)
           , (foldr' <$> undefined <*> generateInt'  <*> undefined , 0)
           ]
    generateInt' = generateInt (d - 1)

generateBool :: MonadRandom m => ExprGenerator m vs Bool
generateBool d | d <= 0 = bB <$> getRandom
               | otherwise = join (fromList gens)
  where
    gens = [ (bB <$> getRandom                                     , 1)
           , (not' <$> generateBool'                               , 1)
           , (fst' <$> undefined                                   , 0)
           , (snd' <$> undefined                                   , 0)
           , ((~<=) <$> generateInt' <*> generateInt'              , 1)
           , ((~<) <$> generateInt' <*> generateInt'               , 1)
           , ((~==) <$> generateInt' <*> generateInt'              , 1)
           , ((~&&) <$> generateBool' <*> generateBool'            , 1)
           , ((~||) <$> generateBool' <*> generateBool'            , 1)
           , (xor' <$> generateBool' <*> generateBool'             , 1)
           , ((~$) <$> undefined <*> undefined                     , 0)
           , (generateIf generateBool d                            , 1)
           , (case' <$> undefined <*> undefined <*> undefined      , 0)
           , (foldr' <$> undefined <*> generateBool' <*> undefined , 0)
           ]
    generateBool' = generateBool (d - 1)
    generateInt' = generateInt (d - 1)

-- this is kind of silly, heh
generateUnit :: MonadRandom m => ExprGenerator m vs ()
generateUnit d | d <= 0    = return unit'
               | otherwise = join (fromList gens)
  where
    gens = [ (return unit'                                         , 1)
           , (fst' <$> undefined                                   , 0)
           , (snd' <$> undefined                                   , 0)
           , ((~$) <$> undefined <*> undefined                     , 0)
           , (generateIf generateUnit d                            , 1)
           , (case' <$> undefined <*> undefined <*> undefined      , 0)
           , (foldr' <$> undefined <*> generateUnit' <*> undefined , 0)
           ]
    generateUnit' = generateUnit (d - 1)

generateList :: MonadRandom m => ExprGenerator m vs a -> ExprGenerator m vs [a]
generateList gx d | d <= 0    = return nil'
                  | otherwise = join (fromList gens)
  where
    gens = [ (return nil'                                                   , 0.01)
           , ((~:) <$> gx' <*> generateList'                                , 1)
           , ((~$) <$> undefined <*> undefined                              , 0)
           , (generateIf (generateList gx) d                                , 1)
           , (case' <$> undefined <*> undefined <*> undefined               , 0)
           , (foldr' <$> undefined <*> generateList' <*> undefined          , 0)
           , (unfoldrN' <$> generateInt (d - 1) <*> undefined <*> undefined , 0)
           , (map' <$> undefined <*> undefined                              , 0)
           , (mapMaybe' <$> undefined <*> undefined                         , 0)
           , (filter' <$> undefined <*> undefined                           , 0)
           , ((~++) <$> generateList' <*> generateList'                     , 1)
           , (take' <$> (abs <$> generateInt (d - 1)) <*> generateList'     , 1)
           ]
    gx'           = gx (d - 1)
    generateList' = generateList gx (d - 1)

generateTuple :: MonadRandom m
              => ExprGenerator m vs a
              -> ExprGenerator m vs b
              -> ExprGenerator m vs (a, b)
generateTuple gx gy d | d <= 0    = tup' <$> gx 0 <*> gy 0
                      | otherwise = join (fromList gens)
  where
    gens = [ (tup' <$> gx' <*> gy'                                  , 1)
           , ((~$) <$> undefined <*> undefined                      , 0)
           , (generateIf (generateTuple gx gy) d                    , 1)
           , (case' <$> undefined <*> undefined <*> undefined       , 0)
           , (foldr' <$> undefined <*> generateTuple' <*> undefined , 0)
           ]
    gx' = gx (d - 1)
    gy' = gy (d - 1)
    generateTuple' = generateTuple gx gy (d - 1)

-- what about cases for div, mod?
generateEither :: MonadRandom m
               => ExprGenerator m vs a
               -> ExprGenerator m vs b
               -> ExprGenerator m vs (Either a b)
generateEither gx gy d | d <= 0    = join . fromList $ [ (left' <$> gx 0 , 1)
                                                       , (right' <$> gy 0, 1)
                                                       ]
                       | otherwise = join (fromList gens)
  where
    gens = [ (left' <$> gx'                                          , 1)
           , (right' <$> gy'                                         , 1)
           , ((~$) <$> undefined <*> undefined                       , 0)
           , (generateIf (generateEither gx gy) d                    , 1)
           , (case' <$> undefined <*> undefined <*> undefined        , 0)
           , (foldr' <$> undefined <*> generateEither' <*> undefined , 0)
           ]
    gx' = gx (d - 1)
    gy' = gy (d - 1)
    generateEither' = generateEither gx gy (d - 1)

generateFunc :: forall a b vs m. MonadRandom m => EType (a -> b) -> ExprGenerator m vs (a -> b)
generateFunc e d = case e of
    EFunc EInt EInt   -> fromList' e [ (return id', 1)
                                     , (return $ λ .-> abs (V IZ), 1)
                                     , (return $ λ .-> signum (V IZ), 1)
                                     , (λ . (+ V IZ) <$> generateInt d', 1)
                                     , (λ . (* V IZ) <$> generateInt d', 1)
                                     , (λ . subtract (V IZ) <$> generateInt d', 1)
                                     , (λ . (V IZ -) <$> generateInt d', 1)
                                     ]
    EFunc EInt EBool  -> fromList' e [ (λ . (`divides'` V IZ) <$> generateInt d', 1)
                                     , (λ . (V IZ `divides'`) <$> generateInt d', 1)
                                     , (λ . (V IZ ~<=) <$> generateInt d', 1)
                                     , (λ . (V IZ ~<) <$> generateInt d', 1)
                                     , (λ . (V IZ ~==) <$> generateInt d', 1)
                                     -- okay
                                     , ((~.) <$> generateFunc e d' <*> generateFunc (EFunc EInt EInt) d', 1)
                                     ]
    EFunc EBool EBool -> fromList' e [ (return id', 1)
                                     , (return $ λ .-> not' (V IZ), 1)
                                     , (λ . (V IZ ~&&) <$> generateBool d', 1)
                                     , (λ . (V IZ ~||) <$> generateBool d', 1)
                                     , (λ . xor' (V IZ) <$> generateBool d', 1)
                                     ]
    EFunc EBool y     -> fromList' e [ ((\t f -> λ .-> if' (V IZ) t f) <$> genFromEType y d' <*> genFromEType y d', 1) ]
    EFunc a (EEither a b) -> undefined
  where
    fromList' :: forall c d. EType (c -> d) -> [(m (Expr vs (c -> d)), Rational)] -> m (Expr vs (c -> d))
    fromList' t gens = join . fromList $ gens0 t ++ gens
    gens0 :: forall c d. EType (c -> d) -> [(m (Expr vs (c -> d)), Rational)]
    gens0 t@(EFunc _ y) = [ (const' <$> genFromEType y d', 1)
                          , (generateIf (generateFunc t) d, 1)
                          , (case' <$> undefined <*> undefined <*> undefined, 0)
                          , (foldr' <$> undefined <*> generateFunc t d' <*> undefined, 0)
                          ]
    d' = max 0 (d - 1)

-- generateIntToInt :: MonadRandom m => ExprGenerator m vs (Int -> Int)
-- generateIntToInt d | d <= 0    = join . fromList $ [ (return $ λ .-> V IZ, 1)
--                                                    , (λ <$> generateInt 0, 1)
--                                                    ]
--                    | otherwise = join (fromList gens)
--   where
--     gens = [ (return $ λ .-> V IZ, 1)
--            , (λ <$> generateInt (d - 1), 1)
--            , ((\i -> λ .-> i + V IZ) <$> generateInt (d - 1), 1)
--            , ((\i -> λ .-> i * V IZ) <$> generateInt (d - 1), 1)
--            ]

generateETypeW :: MonadRandom m => Int -> m ETypeW
generateETypeW d | d <= 0    = join (fromList gens0)
                 | otherwise = join (fromList gens)
  where
    gens0 = [ (return (ETW EInt) , 1)
            , (return (ETW EBool), 1)
            , (return (ETW EUnit), 1)
            ]
    gens  = gens0
         ++ [ ((\(ETW t1) (ETW t2) -> ETW (ETup t1 t2)) <$> generateETypeW' <*> generateETypeW'    , 1)
            , ((\(ETW t1) (ETW t2) -> ETW (EEither t1 t2)) <$> generateETypeW' <*> generateETypeW' , 1)
            , ((\(ETW t1) (ETW t2) -> ETW (EFunc t1 t2)) <$> generateETypeW' <*> generateETypeW'   , 1)
            , ((\(ETW t) -> ETW (EList t)) <$> generateETypeW'                                     , 1)
            ]
    generateETypeW' = generateETypeW (d - 1)

generateExprW :: MonadRandom m => Int -> m ExprW
generateExprW d = do
    ETW t <- generateETypeW 2
    EW t <$> genFromEType t d

genFromEType :: MonadRandom m => EType a -> ExprGenerator m vs a
genFromEType EInt = generateInt
genFromEType EBool = generateBool
genFromEType EUnit = generateUnit
genFromEType (EList x) = generateList (genFromEType x)
genFromEType (ETup x y) = generateTuple (genFromEType x) (genFromEType y)
genFromEType (EEither x y) = generateEither (genFromEType x) (genFromEType y)
genFromEType (EFunc _ _) = undefined
