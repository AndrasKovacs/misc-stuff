
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

data (+) :: forall k. Ixed k -> Ixed k -> Ixed (k, k) where
  L :: f i j a -> (f + g) (i





-- ftcApp :: FTCQueue (Eff fs) i j a b -> a -> Eff fs i j b
-- ftcApp f a = case viewl f of
--   TOne k -> k a
--   k :| t -> case k a of
--     Pure a       -> ftcApp t a
--     Impure cmd k -> Impure cmd (k >< t)    

-- data Eff :: forall ks. IxNP ks -> Ixed (HList ks) where
--   Pure   :: a -> Eff fs is is a
--   Impure :: Sum fs is js a -> FTCQueue (Eff fs) js ks a b -> Eff fs is ks b

-- instance IxFunctor (Eff fs) where
--   imap f (Pure a)     = Pure (f a)
--   imap f (Impure a g) = Impure a (g |> (Pure . f))
  
-- instance IxPointed (Eff fs) where
--   ireturn = Pure
  
-- instance IxApplicative (Eff fs) where
--   iap (Pure f)     a  = imap (f $) a
--   iap (Impure a f) m  = Impure a (f |> (`imap` m))
  
-- instance IxMonad (Eff fs) where
--   ibind f (Pure a)     = f a
--   ibind f (Impure a g) = Impure a (g |> f)

-- send ::
--   forall k ks (f :: Ixed k)(fs :: IxNP ks) i is j js a.
--   Elem f fs i is j js => f i j a -> Eff fs is js a
-- send f = Impure (inj f) (Leaf Pure)









