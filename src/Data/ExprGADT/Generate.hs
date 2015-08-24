{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.ExprGADT.Generate where

import Control.Monad.Random
import Data.ExprGADT.Types
import Data.ExprGADT.Expr
import Data.ExprGADT.Eval
import Control.Monad

type ExprGenerator m vs a = Int -> m (Expr vs a)

type ExprGenerators m vs a = Int -> [(m (Expr vs a), Rational)]

genFromEType :: MonadRandom m => EType a -> ExprGenerator m vs a
genFromEType e = join . fromList . etGenerators e

etGenerators :: forall m vs a. MonadRandom m => EType a -> ExprGenerators m vs a
etGenerators t = do
    pGens <- polyGenerators t
    tGens <- case t of
               EInt          -> concat <$> sequence [intGenerators]
               EBool         -> concat <$> sequence [boolGenerators]
               EUnit         -> concat <$> sequence [unitGenerators]
               EList t1      -> concat <$> sequence [listGenerators t1]
               ETup t1 t2    -> concat <$> sequence [tupleGenerators t1 t2]
               EEither t1 t2 -> concat <$> sequence [eitherGenerators t1 t2]
    return (pGens ++ tGens)

polyGenerators :: MonadRandom m => EType a -> ExprGenerators m vs a
polyGenerators t d = [ (fst' <$> undefined                               , 0)
                     , (snd' <$> undefined                               , 0)
                     , ((~$) <$> undefined <*> undefined                 , 0)
                     , (if' <$> generateBool <*> generateX <*> generateX , 1)
                     , (case' <$> undefined <*> undefined <*> undefined  , 0)
                     , (foldr' <$> undefined <*> generateX <*> undefined , 0)
                     ]
  where
    generateBool = genFromEType EBool (d - 1)
    generateX    = genFromEType t (d - 1)

intGenerators :: MonadRandom m => ExprGenerators m vs Int
intGenerators d = (iI <$> getRandomR (-20, 20), 1)
                : if d > 0 then gens else []
  where
    gens = [ (abs <$> generateInt                                , 1)
           , (signum <$> generateInt                             , 1)
           , (fst' <$> undefined                                 , 0)
           , (snd' <$> undefined                                 , 0)
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
    gens = [ ((~:) <$> generateX <*> generateList              , 1)
           , (map' <$> undefined <*> undefined                 , 0)
           , (mapMaybe' <$> undefined <*> undefined            , 0)
           , (filter' <$> undefined <*> generateList           , 0)
           , ((~++) <$> generateList <*> generateList          , 1)
           , (take' <$> (abs <$> generateInt) <*> generateList , 1)
           , (unfoldrN' <$> generateInt <*> undefined <*> undefined, 0)
           , (unfoldrNUntil' <$> generateInt <*> undefined <*> undefined, 0)
           ]
    generateX    = genFromEType t (d - 1)
    generateList = genFromEType (EList t) (d - 1)
    generateInt  = genFromEType EInt (d - 1)

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

int2IntGenerators :: MonadRandom m => ExprGenerators m vs (Int -> Int)
int2IntGenerators d = gens
  where
    gens = [ (return $ λ .-> abs (V IZ), 1)
           , (return $ λ .-> signum (V IZ), 1)
           , (λ . (+ V IZ) <$> generateInt, 1)
           , (λ . (* V IZ) <$> generateInt, 1)
           , (λ . subtract (V IZ) <$> generateInt, 1)
           , (λ . (V IZ -) <$> generateInt, 1)
           ]
    generateInt = genFromEType EInt (d - 1)

int2BoolGenerators :: MonadRandom m => ExprGenerators m vs (Int -> Bool)
int2BoolGenerators d = gens
  where
    gens = [ (λ . (`divides'` V IZ) <$> generateInt, 1)
           , (λ . (V IZ `divides'`) <$> generateInt, 1)
           , (λ . (V IZ ~<=) <$> generateInt, 1)
           , (λ . (V IZ ~<) <$> generateInt, 1)
           , (λ . (V IZ ~==) <$> generateInt, 1)
           ]
    generateInt = genFromEType EInt (d - 1)

bool2BoolGenerators :: MonadRandom m => ExprGenerators m vs (Bool -> Bool)
bool2BoolGenerators d = gens
  where
    gens = [ (return $ λ .-> not' (V IZ), 1)
           , (λ . (V IZ ~&&) <$> generateBool, 1)
           , (λ . (V IZ ~||) <$> generateBool, 1)
           , (λ . xor' (V IZ) <$> generateBool, 1)
           ]
    generateBool = genFromEType EBool (d - 1)

int2ListGenerators :: MonadRandom m => EType a -> ExprGenerators m vs (Int -> [a])
int2ListGenerators t d = gens
  where
    gens = [ (λ . take' (abs (V IZ)) <$> generateList, 1)
           , ((\f z -> λ .-> unfoldrN' (V IZ) f z) <$> undefined <*> undefined, 0)
           , ((\f z -> λ .-> unfoldrNUntil' (V IZ) f z) <$> undefined <*> undefined, 0)
           ]
    generateList = genFromEType (EList t) (d - 1)

bool2AnyGenerators :: MonadRandom m => EType a -> ExprGenerators m vs (Bool -> a)
bool2AnyGenerators t d = [ (gen, 1) ]
  where
    gen = do
      x <- genFromEType t (d - 1)
      y <- genFromEType t (d - 1)
      return $ λ .-> if' (V IZ) x y

any2TupleGenerators :: MonadRandom m => EType a -> EType b -> EType c -> ExprGenerators m vs (a -> (b, c))
any2TupleGenerators t1 t2 t3 d = [(gen, 1)]
  where
    gen = do
      f <- genFromEType (EFunc t1 t2) (d - 1)
      g <- genFromEType (EFunc t1 t3) (d - 1)
      return $ λ .-> tup' (f ~$ V IZ) (g ~$ V IZ)

either2AnyGenerators :: MonadRandom m => EType a -> EType b -> EType c -> ExprGenerators m vs (Either a b -> c)
either2AnyGenerators t1 t2 t3 d = [ (gen, 1) ]
  where
    gen = do
      f <- genFromEType (EFunc t1 t3) (d - 1)
      g <- genFromEType (EFunc t2 t3) (d - 1)
      return $ λ .-> case' (V IZ) f g

    -- gens = [ ((~:) <$> generateX <*> generateList              , 1)
    --        , (map' <$> undefined <*> undefined                 , 0)
    --        , (mapMaybe' <$> undefined <*> undefined            , 0)
    --        , (filter' <$> undefined <*> generateList           , 0)
    --        , ((~++) <$> generateList <*> generateList          , 1)
    --        , (take' <$> (abs <$> generateInt) <*> generateList , 1)
    --        ]

-- generateFunc :: forall a b vs m. MonadRandom m => EType (a -> b) -> ExprGenerator m vs (a -> b)
-- generateFunc e d = case e of
--     EFunc EInt EInt   -> fromList' e [ (return id', 1)
--                                      , (return $ λ .-> abs (V IZ), 1)
--                                      , (return $ λ .-> signum (V IZ), 1)
--                                      , (λ . (+ V IZ) <$> generateInt d', 1)
--                                      , (λ . (* V IZ) <$> generateInt d', 1)
--                                      , (λ . subtract (V IZ) <$> generateInt d', 1)
--                                      , (λ . (V IZ -) <$> generateInt d', 1)
--                                      ]
--     EFunc EInt EBool  -> fromList' e [ (λ . (`divides'` V IZ) <$> generateInt d', 1)
--                                      , (λ . (V IZ `divides'`) <$> generateInt d', 1)
--                                      , (λ . (V IZ ~<=) <$> generateInt d', 1)
--                                      , (λ . (V IZ ~<) <$> generateInt d', 1)
--                                      , (λ . (V IZ ~==) <$> generateInt d', 1)
--                                      -- okay
--                                      , ((~.) <$> generateFunc e d' <*> generateFunc (EFunc EInt EInt) d', 1)
--                                      ]
--     EFunc EBool EBool -> fromList' e [ (return id', 1)
--                                      , (return $ λ .-> not' (V IZ), 1)
--                                      , (λ . (V IZ ~&&) <$> generateBool d', 1)
--                                      , (λ . (V IZ ~||) <$> generateBool d', 1)
--                                      , (λ . xor' (V IZ) <$> generateBool d', 1)
--                                      ]
--     EFunc EBool y     -> fromList' e [ ((\t f -> λ .-> if' (V IZ) t f) <$> genFromEType y d' <*> genFromEType y d', 1) ]
--     EFunc a (EEither a b) -> undefined
--   where
--     fromList' :: forall c d. EType (c -> d) -> [(m (Expr vs (c -> d)), Rational)] -> m (Expr vs (c -> d))
--     fromList' t gens = join . fromList $ gens0 t ++ gens
--     gens0 :: forall c d. EType (c -> d) -> [(m (Expr vs (c -> d)), Rational)]
--     gens0 t@(EFunc _ y) = [ (const' <$> genFromEType y d', 1)
--                           , (generateIf (generateFunc t) d, 1)
--                           , (case' <$> undefined <*> undefined <*> undefined, 0)
--                           , (foldr' <$> undefined <*> generateFunc t d' <*> undefined, 0)
--                           ]
--     d' = max 0 (d - 1)

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

-- generateETypeW :: MonadRandom m => Int -> m ETypeW
-- generateETypeW d | d <= 0    = join (fromList gens0)
--                  | otherwise = join (fromList gens)
--   where
--     gens0 = [ (return (ETW EInt) , 1)
--             , (return (ETW EBool), 1)
--             , (return (ETW EUnit), 1)
--             ]
--     gens  = gens0
--          ++ [ ((\(ETW t1) (ETW t2) -> ETW (ETup t1 t2)) <$> generateETypeW' <*> generateETypeW'    , 1)
--             , ((\(ETW t1) (ETW t2) -> ETW (EEither t1 t2)) <$> generateETypeW' <*> generateETypeW' , 1)
--             , ((\(ETW t1) (ETW t2) -> ETW (EFunc t1 t2)) <$> generateETypeW' <*> generateETypeW'   , 1)
--             , ((\(ETW t) -> ETW (EList t)) <$> generateETypeW'                                     , 1)
--             ]
--     generateETypeW' = generateETypeW (d - 1)

-- generateExprW :: MonadRandom m => Int -> m ExprW
-- generateExprW d = do
--     ETW t <- generateETypeW 2
--     EW t <$> genFromEType t d

-- genFromEType :: MonadRandom m => EType a -> ExprGenerator m vs a
-- genFromEType EInt = generateInt
-- genFromEType EBool = generateBool
-- genFromEType EUnit = generateUnit
-- genFromEType (EList x) = generateList (genFromEType x)
-- genFromEType (ETup x y) = generateTuple (genFromEType x) (genFromEType y)
-- genFromEType (EEither x y) = generateEither (genFromEType x) (genFromEType y)
-- genFromEType (EFunc _ _) = undefined
