{-# language
  TypeOperators, DataKinds, PolyKinds,
  RankNTypes, EmptyCase, ScopedTypeVariables,
  DeriveFunctor, StandaloneDeriving, GADTs,
  TypeFamilies, FlexibleContexts, FlexibleInstances #-}

type Rep a = Fix (SOP (Code a))

class Generic a where
  type Code a :: [[Maybe *]]
  to   :: a -> Rep a
  from :: Rep a -> a

data NP (ts :: [Maybe *]) (k :: *) where
  Nil  :: NP '[] k
  (:>) :: t -> NP ts k -> NP (Just t ': ts) k
  Rec  :: k -> NP ts k -> NP (Nothing ': ts) k
infixr 5 :>

data SOP (code :: [[Maybe *]]) (k :: *) where
  Z :: NP ts k -> SOP (ts ': code) k
  S :: SOP code k -> SOP (ts ': code) k

deriving instance Functor (SOP code)
deriving instance Functor (NP code)

newtype Fix f = In {out :: f (Fix f)}

cata :: Functor f => (f a -> a) -> Fix f -> a
cata phi = go where go = phi . fmap go . out

type family CurryNP (ts :: [Maybe *]) (r :: *) :: * where
  CurryNP '[]             r = r
  CurryNP (Just t  ': ts) r = t -> CurryNP ts r
  CurryNP (Nothing ': ts) r = r -> CurryNP ts r

type family Alg (code :: [[Maybe *]]) (r :: *) :: * where
  Alg '[]         r = ()
  Alg (ts ': tss) r = (CurryNP ts r, Alg tss r)

(<:) :: a -> b -> (a, b)
(<:) = (,)
infixr 5 <:

uncurryNP :: CurryNP ts a -> NP ts a -> a
uncurryNP f Nil        = f
uncurryNP f (x :> xs)  = uncurryNP (f x) xs
uncurryNP f (Rec k xs) = uncurryNP (f k) xs

algSOP :: Alg code a -> SOP code a -> a
algSOP fs (Z np)  = uncurryNP (fst fs) np
algSOP fs (S sop) = algSOP (snd fs) sop

gcata :: Generic a => Alg (Code a) r -> a -> r
gcata f = cata (algSOP f) . to

instance Generic (Fix (SOP code)) where
  type Code (Fix (SOP code)) = code
  to   = id
  from = id

instance Generic [a] where
  type Code [a] = ['[], [Just a, Nothing]]
  to   = foldr (\x xs -> In (S (Z (x :> Rec xs Nil)))) (In (Z Nil))
  from = gcata ([] <: (:) <: ())


