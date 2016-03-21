
{-# language
  TypeOperators, DataKinds, PolyKinds,
  RankNTypes, EmptyCase, ScopedTypeVariables,
  DeriveFunctor, StandaloneDeriving, GADTs,
  TypeFamilies, FlexibleContexts, FlexibleInstances #-}

type f ~> g = forall i. f i -> g i

type Rep a i = Fix (SOP (Code a)) i

class Generic (a :: i -> *) where
  type Code a :: [(i, [Maybe *])]
  to   :: a ~> Rep a
  from :: Rep a ~> a

class IxFunctor (f :: (k -> *) -> (k -> *)) where
   imap :: (a ~> b) -> (f a ~> f b)

newtype Fix f i = In {out :: f (Fix f) i}

newtype K a i = K a deriving (Functor)

cata :: IxFunctor f => (forall i. f a i -> a i) -> Fix f ~> a
cata phi = phi . imap (cata phi) . out

data NP :: [Maybe *] -> (i -> *) -> i -> * where
  Nil  :: NP '[] k i
  (:>) :: t   -> NP ts k i -> NP (Just t  ': ts) k i
  Rec  :: k i -> NP ts k i -> NP (Nothing ': ts) k i
infixr 5 :>

data SOP :: [(i, [Maybe *])] -> (i -> *) -> i -> * where
  Z :: NP con k i   -> SOP ('(i, con) ': code) k i
  S :: SOP code k i -> SOP (con ': code) k i

instance IxFunctor (NP con) where
  imap f Nil        = Nil
  imap f (x :> xs)  = x :> imap f xs
  imap f (Rec x xs) = Rec (f x) (imap f xs)

instance IxFunctor (SOP code) where
  imap f (Z np)  = Z (imap f np)
  imap f (S sop) = S (imap f sop)

type family CurryNP (con :: (i, [Maybe *])) (r :: i -> *) :: * where
  CurryNP '(i, '[])             r = r i
  CurryNP '(i, (Just t  ': ts)) r = t   -> CurryNP '(i, ts) r
  CurryNP '(i, (Nothing ': ts)) r = r i -> CurryNP '(i, ts) r

-- type family Alg (code :: [[Maybe *]]) (r :: *) :: * where
--   Alg '[]         r = ()
--   Alg (ts ': tss) r = (CurryNP ts r, Alg tss r)

-- (<:) :: a -> b -> (a, b)
-- (<:) = (,)
-- infixr 5 <:

-- uncurryNP :: CurryNP ts a -> NP ts a -> a
-- uncurryNP f Nil        = f
-- uncurryNP f (x :> xs)  = uncurryNP (f x) xs
-- uncurryNP f (Rec k xs) = uncurryNP (f k) xs

-- algSOP :: Alg code a -> SOP code a -> a
-- algSOP fs (Z np)  = uncurryNP (fst fs) np
-- algSOP fs (S sop) = algSOP (snd fs) sop

-- gcata :: Generic a => Alg (Code a) r -> a -> r
-- gcata f = cata (algSOP f) . to

-- instance Generic (Fix (SOP code)) where
--   type Code (Fix (SOP code)) = code
--   to   = id
--   from = id

-- instance Generic [a] where
--   type Code [a] = ['[], [Just a, Nothing]]
--   to   = foldr (\x xs -> In (S (Z (x :> Rec xs Nil)))) (In (Z Nil))
--   from = gcata ([] <: (:) <: ())


