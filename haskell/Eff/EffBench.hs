{-# language
  RankNTypes, LambdaCase, BangPatterns, ScopedTypeVariables,
  TypeApplications, MultiParamTypeClasses, FlexibleInstances,
  FlexibleContexts #-}

import qualified Control.Monad.State.Strict as S
import Criterion.Main
import System.Random


times :: Monad m => Int -> m a -> m ()
times n ma = go n where
  go 0 = pure ()
  go n = ma >> go (n - 1)
{-# inline times #-}


-- inlined church free state
--------------------------------------------------------------------------------

newtype CS s a = CS {runCS ::
     forall r.
     (a -> r)          -- pure
  -> ((s -> r) -> r)   -- get
  -> (s -> r -> r)     -- put
  -> r
  }

instance Functor (CS s) where
  fmap f (CS g) = CS $ \pure get put -> g (pure . f) get put
  {-# inline fmap #-}

instance Applicative (CS s) where
  pure a = CS $ \pure get put -> pure a
  {-# inline pure #-}
  CS mf <*> CS ma = CS $ \pure get put ->
    mf (\f -> ma (pure . f) get put) get put
  {-# inline (<*>) #-}

instance Monad (CS s) where
  return a = CS $ \pure get put -> pure a
  {-# inline return #-}
  CS ma >>= f = CS $ \pure get put ->
    ma (\a -> runCS (f a) pure get put) get put
  {-# inline (>>=) #-}
  CS ma >> CS mb = CS $ \pure get put -> ma (\_ -> mb pure get put) get put
  {-# inline (>>) #-}

cmodify :: (s -> s) -> CS s ()
cmodify f = CS $ \pure get put ->
  get $ \s -> let !s' = f s in
  put s' $
  pure ()
{-# inline cmodify #-}

crunState :: CS s a -> s -> (a, s)
crunState (CS f) = f
  (\a s -> (a, s))
  (\got s -> got s s)
  (\s' put s -> put s')
{-# inline crunState #-}

-- Classy chruch state
--------------------------------------------------------------------------------

class PureD r a where cpure :: a -> r
class GetD  s r where cget  :: (s -> r) -> r
class PutD  s r where cput  :: s -> r -> r

csmodify :: (GetD s r, PutD s r, PureD r ()) => (s -> s) -> r
csmodify f = cget $ \s -> let !s' = f s in cput s' $ cpure ()

cstimes :: forall r. (GetD Int r, PutD Int r, PureD r ()) => Int -> r
cstimes 0 = cpure ()
cstimes n = cget @Int $ \s -> let !s' = s + 1 in cput @Int s' $ cstimes (n - 1)

instance PureD (s -> (a, s)) a where
  cpure a s = (a, s)
  {-# inline cpure #-}
instance GetD  s (s -> (a, s)) where
  cget got s = got s s
  {-# inline cget #-}
instance PutD s (s -> (a, s)) where
  cput s' r _ = r s'
  {-# inline cput #-}

-- inlined free state
--------------------------------------------------------------------------------

data FS s a = Pure a | Get (s -> FS s a) | Put !s (FS s a)

instance Functor (FS s) where
  fmap f = go where
    go = \case
      Pure a  -> Pure (f a)
      Get k   -> Get (fmap f . k)
      Put s k -> Put s (fmap f k)
  {-#  inline fmap #-}

instance Applicative (FS s) where
  pure = Pure
  Pure f  <*> ma = fmap f ma
  Get k   <*> ma = Get ((<*> ma) . k)
  Put s k <*> ma = Put s (k <*> ma)
  {-# inline pure #-}
  {-# inline (<*>) #-}

instance Monad (FS s) where
  return = Pure
  Pure a  >>= f = f a
  Get k   >>= f = Get ((>>= f) . k)
  Put s k >>= f = Put s (k >>= f)
  {-# inline return #-}
  {-# inline (>>=) #-}

fmodify :: (s -> s) -> FS s ()
fmodify f =
  Get $ \s ->
  Put (f s) $
  Pure ()
{-# inline fmodify #-}

frunState :: FS s a -> s -> (a, s)
frunState (Pure a)   s = (a, s)
frunState (Get k)    s = frunState (k s) s
frunState (Put s' k) s = frunState k s'

-- inlined van Laarhoven free state
--------------------------------------------------------------------------------

newtype S s a = S {runS :: s -> (a, s)}

newtype VS s a = VS { runVS ::
     forall m.
     (forall a. a -> m a)                   -- pure
  -> (forall a b. m a -> (a -> m b) -> m b) -- bind
  -> (m s)                                  -- get
  -> (s -> m ())                            -- put
  -> m a
  }

instance Functor (VS s) where
  fmap f (VS g) = VS $ \pure (>>=) get put ->
    g pure (>>=) get put >>= \a -> pure (f a)
  {-# inline fmap #-}

instance Applicative (VS s) where
  pure a = VS $ \pure (>>=) get put -> pure a
  VS mf <*> VS ma = VS $ \pure (>>=) get put ->
    mf pure (>>=) get put >>= \f ->
    ma pure (>>=) get put >>= \a -> pure (f a)
  {-# inline pure #-}
  {-# inline (<*>) #-}

instance Monad (VS s) where
  return a = VS $ \pure (>>=) get put -> pure a
  VS ma >>= f = VS $ \pure (>>=) get put ->
    ma pure (>>=) get put >>= \a -> runVS (f a) pure (>>=) get put
  {-# inline return #-}

vmodify :: (s -> s) -> VS s ()
vmodify f = VS $ \pure (>>=) get put ->
  get >>= \s ->
  let !s' = f s in
  put s'
{-# inline vmodify #-}

vrunState' :: VS s a -> S s a
vrunState' (VS f) = f
  (\a -> S $ \s -> (a, s))
  (\(S ma) f -> S $ \s -> let !(!a, !s') = ma s; !(!b, !s'') = runS (f a) s' in (b, s''))
  (S $ \s -> (s, s))
  (\s' -> S $ \_ -> ((), s'))
{-# inline vrunState' #-}

vrunState :: VS s a -> s -> (a, s)
vrunState x = runS (vrunState' x)
{-# inline vrunState #-}

-- van Laarhoven state translated to mtl State
--------------------------------------------------------------------------------

newtype VSM s a = VSM { runVSM :: forall m. Monad m => m s -> (s -> m ()) -> m a}

instance Functor (VSM s) where
  fmap f (VSM g) = VSM $ \get put ->
    g get put >>= \a -> pure (f a)
  {-# inline fmap #-}

instance Applicative (VSM s) where
  pure a = VSM $ \get put -> pure a
  VSM mf <*> VSM ma = VSM $ \get put ->
    mf get put >>= \f ->
    ma get put >>= \a -> pure (f a)
  {-# inline pure #-}
  {-# inline (<*>) #-}

instance Monad (VSM s) where
  return a = VSM $ \get put -> pure a
  VSM ma >>= f = VSM $ \get put ->
    ma get put >>= \a -> runVSM (f a) get put
  {-# inline return #-}

vmmodify :: (s -> s) -> VSM s ()
vmmodify f = VSM $ \get put ->
  get >>= \s ->
  let !s' = f s in
  put s'
{-# inline vmmodify #-}

vmrunState :: VSM s a -> s -> (a, s)
vmrunState (VSM ma) = S.runState (ma S.get S.put)
{-# inline vmrunState #-}


-- classy van Laarhoven state (same as mtl)
--------------------------------------------------------------------------------

class VPutD s m where vput :: s -> m ()
class VGetD s m where vget :: m s

vmdmodify :: (Monad m, VPutD s m, VGetD s m) => (s -> s) -> m ()
vmdmodify f = do
  s <- vget
  let !s' = f s
  vput s'

instance VPutD s (S.State s) where vput = S.put
instance VGetD s (S.State s) where vget = S.get


-- The Bench
--------------------------------------------------------------------------------

main = do
  (n :: Int) <- randomRIO (10000000, 10000000)

  defaultMain [
    bench "CS" $ whnf (\n -> crunState (times n $ cmodify (+1)) (0 :: Int)) n,
    bench "S"  $ whnf (\n -> S.runState (times n $ S.modify (+1)) (0 :: Int)) n,
    bench "FS" $ whnf (\n -> frunState (times n $ fmodify (+1)) (0 :: Int)) n,
    bench "VS"  $ whnf (\n -> vrunState (times n $ vmodify (+1)) (0 :: Int)) n,
    bench "VSM" $ whnf (\n -> vmrunState (times n $ vmmodify (+1)) (0 :: Int)) n,
    bench "CSD" $ whnf (\n -> cstimes @(Int -> ((), Int)) n (0 :: Int)) n,
    bench "VSD" $ whnf (\n -> S.runState (times n $ vmdmodify @(S.State Int) @Int (+1)) (0 :: Int)) n
    ]
