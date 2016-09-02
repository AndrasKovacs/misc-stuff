{-# language LambdaCase, FlexibleContexts  #-}

-- | Inlined monomorphic Free State monad.

module FreeState where

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

modify :: (s -> s) -> FS s ()
modify f =
  Get $ \s ->
  Put (f s) $
  Pure ()
{-# inline modify #-}

runState :: FS s a -> s -> (a, s)
runState (Pure a)   s = (a, s)
runState (Get k)    s = runState (k s) s
runState (Put s' k) s = runState k s'

