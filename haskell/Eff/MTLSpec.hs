
{-# language FlexibleContexts, BangPatterns, LambdaCase #-}

-- | Compare Core for internal and imported functions with various pragmas

module MTLSpec where

import Control.Monad.State.Strict
import Control.Monad.Reader
import qualified MultiBenchModule as Mod

test1mtl :: MonadState Int m => Int -> m Int
test1mtl n = foldM f 1 [0..n] where
  f acc x | x `rem` 5 == 0 = do
              s <- get
              put $! (s + 1)
              pure $! max acc x
          | otherwise = pure $! max acc x

-- Just looking at Core
--------------------------------------------------------------------------------

-- test1mtl' =
--   flip runState (0 :: Int) . flip runReaderT (0 :: Int) . test1mtl
-- test1mtl_ext' =
--   flip runState (0 :: Int) . flip runReaderT (0 :: Int) . Mod.test1mtl
-- test1mtl_inlinable' =
--   flip runState (0 :: Int) . flip runReaderT (0 :: Int) . Mod.test1mtl_inlinable
-- test1mtl_inline' =
--   flip runState (0 :: Int) . flip runReaderT (0 :: Int) . Mod.test1mtl_inline

