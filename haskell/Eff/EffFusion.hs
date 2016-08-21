{-# language
  RankNTypes, LambdaCase, BangPatterns, ScopedTypeVariables,
  TypeApplications, MultiParamTypeClasses, FlexibleInstances,
  FlexibleContexts, MagicHash, UnboxedTuples, PatternSynonyms,
  DeriveFunctor, UndecidableInstances, ConstraintKinds #-}

import Data.Kind
import Data.Type.Bool

-- newtype CF f a = CF {runCF :: forall r. (a -> r) -> (f r -> r) -> r}

-- instance Functor (CF f) where
--   fmap f (CF ma) = CF $ \pure free -> ma (pure . f) free
--   {-# inline fmap #-}

-- instance Applicative (CF f) where
--   pure a = CF $ \p f -> p a
--   CF mf <*> CF ma = CF $ \pure free ->
--     mf (\f -> ma (pure . f) free) free
--   {-# inline pure #-}
--   {-# inline (<*>) #-}

-- instance Monad (CF f) where
--   return a = CF $ \p f -> p a
--   CF ma >>= f = CF $ \pure free ->
--     ma (\a -> runCF (f a) pure free) free
--   {-# inline return #-}
--   {-# inline (>>=) #-}

-- why not MonadFree f m?
-- why not Church free?

-- newtype Cod m a = Cod {runCod :: forall r. (a -> m r) -> m r} deriving Functor

-- instance Applicative (Cod m) where
--   pure a = Cod $ \k -> k a
--   Cod mf <*> Cod ma = Cod $ \k -> mf $ \f -> ma $ \a -> k (f a)

-- instance Monad (Cod m) where
--   return = pure
--   Cod ma >>= f = Cod $ \k -> ma $ \a -> runCod (f a) k

-- class Functor f => TermAlgebra h f | h -> f where
--   val :: a -> h a
--   con :: f (h a) -> h a

-- type TermMonad m f = (Monad m, TermAlgebra m f)

-- instance TermAlgebra h f => TermAlgebra (Cod h) f where
--   val    = pure
--   con fa = Cod $ \k -> con ((\c -> runCod c k) <$> fa)


-- -- foo ::
--      forall r s a b.
--      ((r -> b) -> b) -- ask
--   -> ((s -> b) -> b) -- get
--   -> (s -> b -> b)   -- put
--   -> (a -> b)        -- pure
--   -> b
-- -- foo ask get put pure =
-- --   ask $ \r ->
-- --   get $ \s ->



-- Untyped preorder traversal of types
--------------------------------------------------------------------------------

data Entry = App | forall a. Con a

type family (xs :: [a]) ++ (ys :: [a]) :: [a] where
  '[]       ++ ys = ys
  (x ': xs) ++ ys = x ': (xs ++ ys)

type family Preord (x :: a) :: [Entry] where
  Preord (f x) = App ': (Preord f ++ Preord x)
  Preord x     = '[ Con x]

-- Find index of unique occurrence, become stuck if occurrence is non-unique or
-- there's no occurrence
--------------------------------------------------------------------------------

data Nat = Z | S Nat

type family (x :: a) == (y :: b) :: Bool where
  x == x = True
  _ == _ = False

type family PreordList (xs :: [a]) (i :: Nat) :: [(Nat, [Entry])] where
  PreordList '[]       _ = '[]
  PreordList (a ': as) i = '(i, Preord a) ': PreordList as (S i)

type family Narrow (e :: Entry) (xs :: [(Nat, [Entry])]) :: [(Nat, [Entry])] where
  Narrow _ '[]                     = '[]
  Narrow e ('(i, e' ': es) ': ess) = If (e == e') '[ '(i, es)] '[] ++ Narrow e ess

type family Find_ (es :: [Entry]) (ess :: [(Nat, [Entry])]) :: Nat where
  Find_ _        '[ '(i, _)] = i
  Find_ (e ': es) ess        = Find_ es (Narrow e ess)

type Find x ys = Find_ (Preord x) (PreordList ys Z)


-- Open functor sums
--------------------------------------------------------------------------------

data NS :: [* -> *] -> * -> * where
  Here  :: f x -> NS (f ': fs) x
  There :: NS fs x -> NS (f ': fs) x

instance Functor (NS '[]) where
  fmap _ = \case {}

instance (Functor f, Functor (NS fs)) => Functor (NS (f ': fs)) where
  fmap f (Here fx)  = Here  (fmap f fx)
  fmap f (There ns) = There (fmap f ns)

class Elem' (n :: Nat) (f :: * -> *) (fs :: [* -> *]) where
  inj' :: forall x. f x -> NS fs x
  prj' :: forall x. NS fs x -> Maybe (f x)

instance (gs ~ (f ': gs')) => Elem' Z f gs where
  inj'           = Here
  prj' (Here fx) = Just fx
  prj' _         = Nothing

instance (Elem' n f gs', (gs ~ (g ': gs'))) => Elem' (S n) f gs where
  inj'            = There . inj' @n
  prj' (Here _)   = Nothing
  prj' (There ns) = prj' @n ns

type family Elems_ fs gs :: Constraint where
  Elems_ '[]       gs = ()
  Elems_ (f ': fs) gs = (Elem' (Find f gs) f gs, Elems_ fs gs)

type Elem  f  fs = (Functor (NS fs), Elem' (Find f fs) f fs)
type Elems fs gs = (Functor (NS gs), Elems_ fs gs)

inj :: forall fs f x. Elem f fs => f x -> NS fs x
inj = inj' @(Find f fs)

prj :: forall f x fs. Elem f fs => NS fs x -> Maybe (f x)
prj = prj' @(Find f fs)

