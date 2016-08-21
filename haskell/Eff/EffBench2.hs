{-# language
  RankNTypes, LambdaCase, BangPatterns, ScopedTypeVariables,
  TypeApplications, MultiParamTypeClasses, FlexibleInstances,
  FlexibleContexts, MagicHash, UnboxedTuples, PatternSynonyms,
  DeriveFunctor #-}

import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Except
import Criterion.Main
import GHC.Prim
import GHC.Types

-- count down from n to 0; throw error at 0
countDown ::
  (MonadState Int m, MonadError Int m, MonadReader Int m) => Int -> m ()
countDown 0 = throwError =<< get
countDown n = do
  m <- ask
  modify' (+m)
  countDown (n - 1)
{-# inlinable countDown #-}

-- RSE
--------------------------------------------------------------------------------

newtype RSE r s e a = RSE {runRSE' :: r -> s -> (# Int#, a, s, e #)}

data Result s e a = Ok a s | Err e

runRSE :: RSE r s e a -> r -> s -> Result s e a
runRSE (RSE ma) r s = case ma r s of
  Ok_ a s -> Ok a s
  Err_ e  -> Err e
{-# inline runRSE #-}

pattern Ok_ a s <- (# 0#, a, s, _ #) where Ok_ a s = (# 0#, a, s, undefined #)
pattern Err_ e  <- (# 1#, _, _, e #) where Err_ e  = (# 1#, undefined, undefined, e #)

instance Functor (RSE r s e) where
  fmap f (RSE g) = RSE $ \r s -> case g r s of
    Ok_ a s -> Ok_ (f a) s
    x       -> unsafeCoerce# x
  {-# inline fmap #-}

instance Applicative (RSE r s e) where
  pure a = RSE $ \r s -> Ok_ a s
  {-# inline pure #-}
  RSE mf <*> RSE ma = RSE $ \r s -> case mf r s of
    Ok_ f s -> case ma r s of
      Ok_ a s -> Ok_ (f a) s
    x -> unsafeCoerce# x
  {-# inline (<*>) #-}

instance Monad (RSE r s e) where
  return a = RSE $ \r s -> Ok_ a s
  {-# inline return #-}
  RSE ma >>= f = RSE $ \r s -> case ma r s of
    Ok_ a s -> runRSE' (f a) r s
    x      -> unsafeCoerce# x
  {-# inline (>>=) #-}

instance MonadState s (RSE r s e) where
  get = RSE $ \r s -> Ok_ s s
  {-# inline get #-}
  put s' = RSE $ \r _ -> Ok_ () s'
  {-# inline put #-}

instance MonadError e (RSE r s e) where
  throwError e = RSE $ \_ _ -> Err_ e
  {-# inline throwError #-}
  catchError (RSE ma) h = RSE $ \r s -> case ma r s of
    Err_ e -> runRSE' (h e) r s
    x      -> x
  {-# inline catchError #-}

instance MonadReader r (RSE r s e) where
  ask = RSE $ \r s -> Ok_ r s
  {-# inline ask #-}
  local f (RSE ma) = RSE $ \r s -> ma (f r) s
  {-# inline local #-}


-- mtl
--------------------------------------------------------------------------------

type RSEMTL1 r s e = ReaderT r (StateT s (Either e))

runRSEMTL1 :: RSEMTL1 r s e a -> r -> s -> Either e (a, s)
runRSEMTL1 ma r s = runStateT (runReaderT ma r) s
{-# inline runRSEMTL1 #-}

type RSEMTL2 r s e = ExceptT e (ReaderT r (State s))

runRSEMTL2 :: RSEMTL2 r s e a -> r -> s -> (Either e a, s)
runRSEMTL2 ma r s = runState (runReaderT (runExceptT ma) r) s
{-# inline runRSEMTL2 #-}


-- main = do
--   let !n = 10000000
--   print $ seq (runRSEMTL2 (countDown n) 10 10) ()

main = do
  let !n = 100000000
  defaultMain [
    bench "RSE"     $ whnf (\n -> runRSE     (countDown n) 10 10) n,
    bench "RSEMTL1" $ whnf (\n -> runRSEMTL1 (countDown n) 10 10) n,
    bench "RSEMTL2" $ whnf (\n -> runRSEMTL2 (countDown n) 10 10) n
    ]

