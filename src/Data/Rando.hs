module Data.Rando where

import Control.Monad.Random

class Rando a where
    rando :: MonadRandom m => Int -> m a
