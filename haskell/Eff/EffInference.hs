
{-# language
  RankNTypes, GADTs, TypeInType, LambdaCase, TypeApplications,
  TypeOperators, StandaloneDeriving, TupleSections, EmptyCase,
  ScopedTypeVariables, TypeFamilies, ConstraintKinds,
  FlexibleContexts, MultiParamTypeClasses, AllowAmbiguousTypes,
  FlexibleInstances, DeriveFunctor, UndecidableInstances,
  NoMonomorphismRestriction #-}

module EffInference where

import Data.Kind
import Data.Type.Bool
import Control.Monad
import Control.Arrow
import Data.Word
import GHC.TypeLits (Symbol)
import Data.Monoid

import Control.Exception (Exception)

-- Examples
--------------------------------------------------------------------------------

-- polymorphic state
test1 = run $ runState 0 $
  modify (+100)

-- multiple monomorphic state
test3 = run $ runState 'a' $ runState True $ do
  c <- get
  put (c == 'a')

-- multiple & polymorphic state
test2 = run $ runState [0..10] $ runState (0 :: Int) $ do
  xs <- get
  put $ length xs

-- This works because we first traverse monomorphic first tuple components
test4 = run $ runState ('a', 0) $ runState (True, 0) $
  put (False, 0)

-- This fails for the same reason
test5 = run $ runState (0, 'a') $ runState (0, True) $ do
  -- put (0, False) -- error, or a unusable type if we have NoMonomorphismRestriction
  pure ()

-- Multiple writer with type applications
test6 = run $ runWriter @String $ runWriter @[Int] $ do
  tell @String "foo"
  tell @[Int] [0..10]

-- Multiple state with type applications
test7 = run $ runState @Int 0 $ runState @Word 0 $ do
  modify @Int (+100)
  modify @Word (+100)

-- Effect shadowing disallowed
test8 = run $ runWriter @String $ runWriter @String $
  -- tell "foo" -- error
  pure ()

-- Labelled state: works the same if there's only one State, but needs mandatory labels
-- if there are more
test9 = run $ lrunState 0 $
  lmodify (+100)

-- But has full type inference if we do specify labels
test10 = run $ lrunState @"x" 0 $ lrunState @"y" 0 $ do
  lmodify @"x" (+100)
  lmodify @"y" (+20)

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
  {-# inline fmap #-}

class Elem' (n :: Nat) (f :: * -> *) (fs :: [* -> *]) where
  inj' :: forall x. f x -> NS fs x
  prj' :: forall x. NS fs x -> Maybe (f x)

instance (gs ~ (f ': gs')) => Elem' Z f gs where
  inj'           = Here
  prj' (Here fx) = Just fx
  prj' _         = Nothing
  {-# inline inj' #-}
  {-# inline prj' #-}

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
{-# inline inj #-}

prj :: forall f x fs. Elem f fs => NS fs x -> Maybe (f x)
prj = prj' @(Find f fs)
{-# inline prj #-}

-- Eff monad
--------------------------------------------------------------------------------

data Eff fs a = Pure a | Free (NS fs (Eff fs a))

deriving instance (Show a, Show (NS fs (Eff fs a))) => Show (Eff fs a)
deriving instance (Eq a, Eq (NS fs (Eff fs a))) => Eq (Eff fs a)
deriving instance (Functor (NS fs)) => Functor (Eff fs)

instance Functor (NS fs) => Applicative (Eff fs) where
  pure          = Pure
  Pure f  <*> b = f <$> b
  Free fs <*> b = Free ((<*> b) <$> fs)
  {-# inline pure #-}
  {-# inline (<*>) #-}

instance Functor (NS fs) => Monad (Eff fs) where
  return = Pure
  Pure a  >>= f = f a
  Free fs >>= f = Free ((>>= f) <$> fs)
  {-# inline return #-}
  {-# inline (>>=) #-}

run :: Eff '[] a -> a
run (Pure a) = a

liftEff :: (Functor f, Elem f fs) => f a -> Eff fs a
liftEff fa = Free (inj (Pure <$> fa))
{-# inline liftEff #-}

cata :: Functor (NS fs) => (a -> r) -> (NS fs r -> r) -> Eff fs a -> r
cata pure free = go where
  go (Pure a)  = pure a
  go (Free ns) = free (go <$> ns)
{-# inline cata #-}

handle ::
     (Functor f, Functor (NS fs))
  => (a -> b) -> (f (Eff fs b) -> Eff fs b)
  -> Eff (f ': fs) a -> Eff fs b
handle pure free = cata (Pure . pure) (\case Here fa -> free fa; There ns -> Free ns)
{-# inlinable handle #-}

interpose ::
     Elem f fs
  => (a -> Eff fs b) -> (f (Eff fs a) -> Eff fs b)
  -> Eff fs a -> Eff fs b
interpose p f = go where
  go (Pure x)  = p x
  go (Free ns) = maybe (Free (go <$> ns)) f (prj ns)
{-# inline interpose #-}

-- State
--------------------------------------------------------------------------------

data State s k = Put s k | Get (s -> k) deriving Functor

runState :: forall s fs a. Functor (NS fs) => s -> Eff (State  s ': fs) a -> Eff fs (a, s)
runState s (Pure a)                 = Pure (a, s)
runState s (Free (Here (Get k)))    = runState s (k s)
runState s (Free (Here (Put s' k))) = runState s' k
runState s (Free (There ns))        = Free (fmap (runState s) ns)

get :: forall s fs. Elem (State s) fs => Eff fs s
-- get = liftEff (Get id)
get = Free (inj (Get Pure))
{-# inline get #-}

put :: forall s fs. Elem (State s) fs => s -> Eff fs ()
-- put s = liftEff (Put s ())
put s = Free (inj (Put s (Pure ())))
{-# inline put #-}

modify :: forall s fs. Elem (State s) fs => (s -> s) -> Eff fs ()
modify f = put =<< f <$> get
{-# inline modify #-}

-- Labelled state
--------------------------------------------------------------------------------

data LState l s k = LPut s k | LGet (s -> k) deriving Functor

lrunState :: forall l s fs a. Functor (NS fs) => s -> Eff (LState l s ': fs) a -> Eff fs (a, s)
lrunState = flip $ cata
  (\a s -> Pure (a, s))
  (\case
      Here (LGet k) -> \s -> k s s
      Here (LPut s' k) -> \_ -> k s'
      There ns -> \s -> Free (($ s) <$> ns))

lget :: forall l s fs. Elem (LState l s) fs => Eff fs s
lget = liftEff (LGet @l id)
{-# inline lget #-}

lput :: forall l s fs. Elem (LState l s) fs => s -> Eff fs ()
lput s = liftEff (LPut @l s ())
{-# inline lput #-}

lmodify :: forall l s fs. Elem (LState l s) fs => (s -> s) -> Eff fs ()
lmodify f = lput @l =<< f <$> lget @l
{-# inline lmodify #-}

-- Reader
--------------------------------------------------------------------------------

newtype Reader r k = Ask (r -> k) deriving Functor

-- runReader :: forall r fs a. Functor (NS fs) => r -> Eff (Reader r ': fs) a -> Eff fs a
-- runReader r = handle id (\(Ask k) -> k r)
-- {-# inline runReader #-}

runReader :: forall r fs a. Functor (NS fs) => r -> Eff (Reader r ': fs) a -> Eff fs a
runReader r (Pure a)              = Pure a
runReader r (Free (Here (Ask k))) = runReader r (k r)
runReader r (Free (There ns))     = Free (fmap (runReader r) ns)

ask :: forall r fs. Elem (Reader r) fs => Eff fs r
ask = liftEff (Ask id)
{-# inline ask #-}

-- The only thing we can't implement efficiently using cata
-- Freer monad neede
local :: forall r fs a. Elem (Reader r) fs => (r -> r) -> Eff fs a -> Eff fs a
local f e = do
  r <- f <$> ask
  interpose Pure (\(Ask k) -> k r) e
{-# inline local #-}

-- Exception
--------------------------------------------------------------------------------

-- newtype Exc e k = Throw e deriving Functor

-- throw :: forall e fs a. Elem (Exc e) fs => e -> Eff fs a
-- throw e = liftEff (Throw e)
-- {-# inline throw #-}

-- runExc :: forall e fs a. Functor (NS fs) => Eff (Exc e ': fs) a -> Eff fs (Either e a)
-- runExc = handle Right (\(Throw e) -> Pure (Left e))
-- {-# inline runExc #-}

-- catch :: Elem (Exc e) fs => Eff fs a -> (e -> Eff fs a) -> Eff fs a
-- catch eff h = cata Pure (\ns -> maybe (Free ns) (\(Throw e) -> h e) (prj ns)) eff
-- {-# inline catch #-}

-- Lift
--------------------------------------------------------------------------------

data Lift m k = forall a. Lift (m a) (a -> k)
deriving instance Functor (Lift m)

lift :: forall m fs a. Elem (Lift m) fs => m a -> Eff fs a
lift ma = liftEff (Lift ma id)

runLift :: forall m a. Monad m => Eff '[Lift m] a -> m a
runLift (Pure a)                  = pure a
runLift (Free (Here (Lift ma k))) = runLift . k =<< ma

-- Writer
--------------------------------------------------------------------------------

data Writer m k = Tell m k deriving (Functor)

tell :: (Monoid m, Elem (Writer m) fs) => m -> Eff fs ()
tell m = liftEff (Tell m ())
{-# inline tell #-}

runWriter :: forall m fs a.
  (Monoid m, Functor (NS fs)) => Eff (Writer m ': fs) a -> Eff fs (a, m)
runWriter = handle (,mempty) (\(Tell m k) -> second (<> m) <$> k)
{-# inline runWriter #-}

--------------------------------------------------------------------------------

data Throw e k = Throw e
  deriving (Functor)

throw :: forall e r a . (Elem (Throw e) r) => e -> Eff r a
throw = liftEff . Throw

catch :: forall e r a . (e -> a) -> Eff (Throw e ': r) a -> Eff r a
catch = undefined

data StrError = StrError String deriving (Show)
data IntError = IntError Int    deriving (Show)

instance Exception StrError
instance Exception IntError

f1 :: forall r. (Elem (Throw StrError) r, Elem (Throw IntError) r) => Int -> Eff r Int
f1 _ = do
    throw (StrError "err")
    throw (IntError 123)

throwIO' :: forall e r a . (Elem IO r, Exception e) => Eff (Throw e ': r) a -> Eff r a
throwIO' = undefined

f1' ::
  (Elem IO r,
   Elem (Throw StrError) (Throw IntError ': r),
   Elem (Throw IntError) (Throw IntError ': r)) => Eff r Int
f1' = throwIO' @IntError (f1 10)

