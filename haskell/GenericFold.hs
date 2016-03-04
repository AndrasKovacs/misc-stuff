-- Works (GHC 8.0)
--------------------------------------------------------------------------------

{-# language
  TypeApplications, TypeOperators, DataKinds, PolyKinds,
  RankNTypes, LambdaCase, EmptyCase, ScopedTypeVariables,
  DeriveFunctor, StandaloneDeriving, GADTs,
  TypeFamilies, FlexibleContexts, FlexibleInstances #-}

data SList xs where
  SNil :: SList '[]
  SCons :: SList xs -> SList (x ': xs)

class SListI (xs :: [k]) where sing :: SList xs
instance SListI '[] where sing = SNil
instance SListI xs => SListI (x ': xs) where sing = SCons sing

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

type family CurryNP (ts :: [Maybe *]) (r :: *) :: * where
  CurryNP '[]             r = r
  CurryNP (Just t  ': ts) r = t -> CurryNP ts r
  CurryNP (Nothing ': ts) r = r -> CurryNP ts r

type family Fold code a r where
  Fold '[]         a r = r
  Fold (ts ': tss) a r = CurryNP ts a -> Fold tss a r
  
uncurryNP :: CurryNP code a -> NP code a -> a
uncurryNP f Nil        = f
uncurryNP f (x :> xs)  = uncurryNP (f x) xs
uncurryNP f (Rec k xs) = uncurryNP (f k) xs

switchFold :: forall a r code.  SList code -> (a -> Fold code r r) -> Fold code r (a -> r)
switchFold SNil         f = f
switchFold (SCons code) f = \x -> switchFold @a @r code (\a -> f a x)

toFold :: forall a code. SList code -> ((SOP code a -> a) -> a) -> Fold code a a
toFold SNil         fsop = fsop (\case {})
toFold (SCons code) fsop =
  \fnp -> toFold code (\f -> fsop (\case Z np -> uncurryNP fnp np; S sop -> f sop))

gcata :: forall a r. Generic a => Fold (Code a) r (a -> r)
gcata = switchFold @a @r code (toFold @r code . flip cata . to)
  where code = sing @_ @(Code a)

gcata1 :: forall f a r. Generic (f a) => Fold (Code (f a)) r (f a -> r)
gcata1 = gcata @(f a) @r

newtype Fix f = In {out :: f (Fix f)}

cata :: Functor f => (f a -> a) -> Fix f -> a
cata phi = go where go = phi . fmap go . out

type Rep a = Fix (SOP (Code a))

class SListI (Code a) => Generic a where
  type Code a :: [[Maybe *]]
  to   :: a -> Rep a
  from :: Rep a -> a

instance Generic (Maybe a) where
  type Code (Maybe a) = ['[Just a], '[]]
  to   = maybe (In (S (Z Nil))) (\a -> In (Z (a :> Nil)))
  from = gcata @(Rep (Maybe a)) Just Nothing

instance SListI code => Generic (Fix (SOP code)) where
  type Code (Fix (SOP code)) = code
  to   = id
  from = id  

instance Generic [a] where
  type Code [a] = ['[], [Just a, Nothing]]  
  to   = foldr (\x xs -> In (S (Z (x :> Rec xs Nil)))) (In (Z Nil))
  from = gcata @(Rep [a]) [] (:)
