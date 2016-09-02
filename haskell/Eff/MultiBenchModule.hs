{-# language FlexibleContexts #-}

-- | mtl function from MultiBench reimplemented and exported
--   to test specialization

module MultiBenchModule where

import Control.Monad.State
import Control.Monad.Reader

test1mtl :: MonadState Int m => Int -> m Int
test1mtl n = foldM f 1 [0..n] where
  f acc x | x `rem` 5 == 0 = do
              s <- get
              put $! (s + 1)
              pure $! max acc x
          | otherwise = pure $! max acc x

test2mtl :: Int -> StateT Int (ReaderT Int (StateT Bool (Reader Bool))) ()
test2mtl n = replicateM_ n $ do
  rint  <- lift $ ask
  rbool <- lift $ lift $ lift ask
  modify' $ \n -> if n < rint && rbool then n + 10 else n + 20
  lift $ lift $ modify' $ \b -> if b then b && rbool else rint < 20


test1mtl_inlinable :: MonadState Int m => Int -> m Int
test1mtl_inlinable n = foldM f 1 [0..n] where
  f acc x | x `rem` 5 == 0 = do
              s <- get
              put $! (s + 1)
              pure $! max acc x
          | otherwise = pure $! max acc x
{-# inlinable test1mtl_inlinable #-}

test2mtl_inlinable :: Int -> StateT Int (ReaderT Int (StateT Bool (Reader Bool))) ()
test2mtl_inlinable n = replicateM_ n $ do
  rint  <- lift $ ask
  rbool <- lift $ lift $ lift ask
  modify' $ \n -> if n < rint && rbool then n + 10 else n + 20
  lift $ lift $ modify' $ \b -> if b then b && rbool else rint < 20
{-# inlinable test2mtl_inlinable #-}


test1mtl_inline :: MonadState Int m => Int -> m Int
test1mtl_inline n = foldM f 1 [0..n] where
  f acc x | x `rem` 5 == 0 = do
              s <- get
              put $! (s + 1)
              pure $! max acc x
          | otherwise = pure $! max acc x
{-# inline test1mtl_inline #-}

test2mtl_inline :: Int -> StateT Int (ReaderT Int (StateT Bool (Reader Bool))) ()
test2mtl_inline n = replicateM_ n $ do
  rint  <- lift $ ask
  rbool <- lift $ lift $ lift ask
  modify' $ \n -> if n < rint && rbool then n + 10 else n + 20
  lift $ lift $ modify' $ \b -> if b then b && rbool else rint < 20
{-# inline test2mtl_inline #-}





