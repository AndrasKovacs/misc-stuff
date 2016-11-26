
{-|
Atkey style indexed extensible effects. Also, we have an open sum of effects that is
indexed by the heterogeneous list of all the indices in the component effects.

It's hairy enough that GHC can't handle it. It's bugged out for even the simplest runner
functions.
-}

{-# language
  RebindableSyntax, UndecidableInstances, TypeInType, TypeApplications,
  AllowAmbiguousTypes, GADTs, TypeFamilies, ScopedTypeVariables,
  UndecidableInstances, LambdaCase, EmptyCase, TypeOperators, ConstraintKinds,
  NoMonomorphismRestriction,
  FlexibleContexts, MultiParamTypeClasses, FlexibleInstances #-}

import Prelude hiding (Monad(..))
import Control.Monad.Indexed
import Data.Kind
import GHC.TypeLits (Symbol)

return :: IxMonad m => a -> m i i a
return = ireturn

(>>=) :: IxMonad m => m i j a -> (a -> m j k b) -> m i k b
(>>=) = (>>>=)

(>>) :: IxApplicative m => m i j a -> m j k b -> m i k b
f >> g = imap (const id) f `iap` g

infixl 1 >>=
infixl 1 >>

-- FastTCQueue reimplementation, because we need to index with arbitrary kinds,
-- not just *. Also specialized to Atkey's indexed types, so we have
-- slightly less confusion with the implementation.
--------------------------------------------------------------------------------  

data FTCQueue f i j a b where
  Leaf :: (a -> f i j b) -> FTCQueue f i j a b
  Node :: FTCQueue f i j a b -> FTCQueue f j k b c -> FTCQueue f i k a c

(|>) :: FTCQueue f i j a b -> (b -> f j k c)  -> FTCQueue f i k a c
t |> r = Node t (Leaf r)

(><) :: FTCQueue f i j a b -> FTCQueue f j k b c -> FTCQueue f i k a c
l >< r = Node l r

data ViewL f i j a b where
  TOne  :: (a -> f i j b) -> ViewL f i j a b
  (:|)  :: (a -> f i j b) -> FTCQueue f j k b c  -> ViewL f i k a c

viewl :: FTCQueue f i j a b -> ViewL f i j a b
viewl (Leaf f)   = TOne f
viewl (Node l r) = go l r
 where
   go :: FTCQueue f i j a b -> FTCQueue f j k b c -> ViewL f i k a c
   go (Leaf r)   t = r :| t
   go (Node l r) t = go l (Node r t)

-- Sums
--------------------------------------------------------------------------------

type Ixed k = k -> k -> * -> *

-- A heterogeneously indexed list for the functors
data IxNP :: [*] -> * where
  INil  :: IxNP '[]
  (:::) :: Ixed k -> IxNP ks -> IxNP (k ': ks)
infixr 5 :::

-- A heterogeneous list for the indices  
data HList :: [*] -> * where
  Nil  :: HList '[]
  (:>) :: a -> HList as -> HList (a ': as)
infixr 5 :>  

-- with explicit ks argument
type Sum' (ks :: [*]) (fs :: IxNP ks) = Sum fs

-- with implicit ks argument
data Sum :: forall (ks :: [*]). IxNP ks -> HList ks -> HList ks -> * -> * where
  Here  :: (f :: Ixed k) i j a -> Sum' (k ': ks) (f ::: fs) (i :> is) (j :> js) a
  There :: Sum' ks fs is js a -> Sum' (k ': ks) (f ::: fs) (i :> is) (j :> js) a

-- Simple find
--------------------------------------------------------------------------------

data Nat = Z | S Nat   

-- only looks at effects, not indices
type family Find k ks (f :: Ixed k)(fs :: IxNP ks) :: Nat where
  Find k (k  ': ks) f (f  ::: fs) = Z
  Find k (k' ': ks) f (f' ::: fs) = S (Find k ks f fs)

-- Inj/prj
--------------------------------------------------------------------------------

class Elem' (n :: Nat) k ks (f :: Ixed k) (fs :: IxNP ks) i is j js where
  inj' :: forall a. f i j a -> Sum fs is js a
  prj' :: forall a. Sum fs is js a -> Maybe (f i j a)
  
instance (fs ~ (f ::: fs'), is ~ (i :> is'), js ~ (j :> js')) =>
  Elem' Z k (k ': ks') f fs i is j js where
  inj'          = Here
  prj' (Here f) = Just f
  prj' _        = Nothing

instance
  (Elem' n k ks f fs' i is' j js', fs ~ (f' ::: fs'), is ~ (i' :> is'), js ~ (j' :> js')) =>
  Elem' (S n) k (k ': ks) f fs i is j js where
  inj'            = There . inj' @n
  prj' (Here _)   = Nothing
  prj' (There ns) = prj' @n ns

type Elem (f :: Ixed k) (fs :: IxNP ks) = Elem' (Find k ks f fs) k ks f fs

type family Elems
  (fs :: IxNP ks) (fs' :: IxNP ks')
  (is :: HList ks) (is' :: HList ks')
  (js :: HList ks) (js' :: HList ks') :: Constraint where
  Elems INil       _    _        _   _         _   = ()
  Elems (f ::: fs) fs' (i :> is) is' (j :> js) js' = (Elem f fs' i is' j js', Elems fs fs' is is' js js')

inj ::
  forall k ks (f :: Ixed k) (fs :: IxNP ks) i is j js a.
  Elem f fs i is j js => f i j a -> Sum' ks fs is js a
inj = inj' @(Find k ks f fs)

prj ::
  forall k ks (f :: Ixed k) (fs :: IxNP ks) i is j js a.
  Elem f fs i is j js => Sum' ks fs is js a -> Maybe (f i j a)
prj = prj' @(Find k ks f fs)

-- Extensible effects
--------------------------------------------------------------------------------

ftcApp :: FTCQueue (Eff fs) i j a b -> a -> Eff fs i j b
ftcApp f a = case viewl f of
  TOne k -> k a
  k :| t -> case k a of
    Pure a       -> ftcApp t a
    Impure cmd k -> Impure cmd (k >< t)    

data Eff :: forall ks. IxNP ks -> Ixed (HList ks) where
  Pure   :: a -> Eff fs is is a
  Impure :: Sum fs is js a -> FTCQueue (Eff fs) js ks a b -> Eff fs is ks b

instance IxFunctor (Eff fs) where
  imap f (Pure a)     = Pure (f a)
  imap f (Impure a g) = Impure a (g |> (Pure . f))
  
instance IxPointed (Eff fs) where
  ireturn = Pure
  
instance IxApplicative (Eff fs) where
  iap (Pure f)     a  = imap (f $) a
  iap (Impure a f) m  = Impure a (f |> (`imap` m))
  
instance IxMonad (Eff fs) where
  ibind f (Pure a)     = f a
  ibind f (Impure a g) = Impure a (g |> f)

send ::
  forall k ks (f :: Ixed k)(fs :: IxNP ks) i is j js a.
  Elem f fs i is j js => f i j a -> Eff fs is js a
send f = Impure (inj f) (Leaf Pure)  

-- Named file operations
--------------------------------------------------------------------------------

data FileStatus = FOpen | FClosed

data File (name :: Symbol) i o a where
  Open  :: File name FClosed FOpen   ()
  Close :: File name FOpen   FClosed ()
  Read  :: File name FOpen   FOpen   String
  Write :: File name FOpen   FOpen   ()

open ::
  forall name ks (fs :: IxNP ks) is js.
  Elem (File name) fs FClosed is FOpen js => Eff fs is js ()
open = send @_ @_ @(File name) Open

close ::
  forall name ks (fs :: IxNP ks) is js.
  Elem (File name) fs FOpen is FClosed js => Eff fs is js ()
close = send @_ @_ @(File name) Close
  
test ::
  Eff (File "foo" ::: File "bar" ::: INil)
      (FClosed :> FClosed :> Nil)
      (FClosed :> FOpen   :> Nil)
      ()
test = do
  open @"foo"
  open @"bar"
  close @"foo"
  -- close @"bar"   -- error : "bar" must be open on return  
  return ()  

-- Unfortunately, we can't run this (even in the simplest way) because of GHC bugs
runFile ::
  Eff (File name ::: fs) (i :> is) (j :> js) a
  -> Eff fs is js a
runFile (Pure a)       = Pure a
runFile (Impure (Here fcmd) k) = case fcmd of
  Open -> undefined -- runFile (ftcApp k ()) -- GHC bug

