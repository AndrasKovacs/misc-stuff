{-# language UndecidableInstances, OverloadedStrings #-}

import Prelude hiding (pi)
import Data.Kind hiding (Type)
import Data.Type.Equality
import Data.String

-- K and I
--------------------------------------------------------------------------------

newtype K a b = K a deriving (Eq, Show, Functor, Foldable, Traversable)
newtype I a   = I a deriving (Eq, Show, Functor, Foldable, Traversable)

instance Applicative I where
  pure = I
  I f <*> I a = I (f a)

getK (K a) = a
getI (I a) = a

--------------------------------------------------------------------------------

type (:->) f g = forall i. f i -> g i

class IxFunctor (f :: (i -> *) -> (i -> *)) where
  imap :: (a :-> b) -> (f a :-> f b)

class IxFunctor f => IxApplicative f where
  ipure :: a :-> f a

class IxApplicative m => IxMonad m where
  (>>-) :: m a i -> (a :-> m b) -> m b i
infixl 1 >>-

class IxFunctor t => IxTraversable t where
  itraverse :: Applicative f => (forall i. a i -> f (b i)) -> (forall i. t a i -> f (t b i))

imapDefault :: IxTraversable t => (a :-> b) -> (t a :-> t b)
imapDefault f = getI . itraverse (I . f)

class IxMonadTrans m where
  ilift :: IxMonad t => t a :-> m t a

class Bound m where
  (>>>-) :: IxMonad t => m t f a -> (f :-> t g) -> m t g a
infixl 1 >>>-

-- Var
--------------------------------------------------------------------------------

data Var b f i = B (b i) | F (f i)

instance IxFunctor (Var b) where
  imap = imapDefault

instance IxTraversable (Var b) where
  itraverse f = \case B b -> pure (B b); F x -> F <$> f x

instance IxApplicative (Var b) where
  ipure = F

instance IxMonad (Var b) where
  F x >>- f = f x
  B b >>- f = B b

deriving instance (Show (b i) , Show (f i)) => Show (Var b f i)
deriving instance (Eq (b i) , Eq (f i)) => Eq (Var b f i)

-- Scope
--------------------------------------------------------------------------------

newtype Scope b f a i = Scope (f (Var b (f a)) i)
unScope (Scope x) = x

instance IxFunctor f => IxFunctor (Scope b f) where
  imap f (Scope fa) = Scope (imap (imap (imap f)) fa)

instance (IxTraversable f) => IxTraversable (Scope b f) where
  itraverse f (Scope fa) = Scope <$> itraverse (itraverse (itraverse f)) fa

instance IxMonadTrans (Scope b) where
  ilift = Scope . ipure . F

instance IxApplicative f => IxApplicative (Scope b f) where
  ipure = Scope . ipure . F . ipure

instance IxMonad f => IxMonad (Scope b f) where
  Scope ma >>- f = Scope $ ma >>- \case
    B b -> ipure $ B b
    F x -> x >>- unScope . f

instance Bound (Scope b) where
  Scope ma >>>- f = Scope (imap (imap (>>- f)) ma)

deriving instance Show (f (Var b (f a)) i) => Show (Scope b f a i)

instance (IxMonad f, Eq (f (Var b a) i)) => Eq (Scope b f a i) where
  a == b = fromScope a == fromScope b

-- Operations on unary binders
--------------------------------------------------------------------------------

type Scope1 j f a i = Scope ((:~:) j) f a i

class EqF f where
  eqF :: f i -> f j -> Maybe (i :~: j)

inst1 :: IxMonad f => f a j -> Scope1 j f a :-> f a
inst1 t' (Scope t) = t >>- \case B Refl -> t'; F x -> x

abs1 :: (IxMonad f, EqF a) => a j -> f a :-> Scope1 j f a
abs1 a = Scope . imap (\a' -> case eqF a a' of
  Just Refl -> B Refl
  Nothing   -> F (ipure a'))

fromScope :: IxMonad f => Scope b f a :-> f (Var b a)
fromScope (Scope t) = t >>- \case
  F x -> imap F x
  B b -> ipure (B b)

toScope :: IxMonad f => f (Var b a) :-> Scope b f a
toScope = Scope . imap (imap ipure)


-- Caclulus of constructions
--------------------------------------------------------------------------------

data Direction = Infer | Check
type Type = Term
type TC = Either String

data Term (a :: Direction -> *) (d :: Direction) where
  -- infer
  Var  :: a d -> Term a d -- forced by IxMonad instance, but we can actually only build Infer
  Star :: Type a Infer
  App  :: Term a Infer -> Term a Check -> Term a Infer
  Pi   :: Type a Check -> Scope1 Infer Type a Check -> Type a Infer
  Ann  :: Term a Check -> Type a Check -> Term a Infer

  -- check
  Inf  :: Term a Infer -> Term a Check
  Lam  :: Scope1 Infer Term a Check -> Term a Check

instance IxFunctor Term where
  imap = imapDefault

instance IxTraversable Term where
  itraverse f = \case
    Var a    -> Var <$> f a
    Star     -> pure Star
    App a b  -> App <$> itraverse f a <*> itraverse f b
    Pi ty t  -> Pi <$> itraverse f ty <*> itraverse f t
    Ann t ty -> Ann <$> itraverse f t <*> itraverse f ty
    Inf t    -> Inf <$> itraverse f t
    Lam t    -> Lam <$> itraverse f t

instance IxApplicative Term where
  ipure = Var

instance IxMonad Term where
  Var a    >>- f = f a
  Star     >>- f = Star
  App a b  >>- f = App (a >>- f) (b >>- f)
  Pi ty t  >>- f = Pi (ty >>- f) (t >>>- f)
  Ann t ty >>- f = Ann (t >>- f) (ty >>- f)
  Inf t    >>- f = Inf (t >>- f)
  Lam t    >>- f = Lam (t >>>- f)

deriving instance (Show (a Check), Show (a Infer), Show (a d)) => Show (Term a d)

--  Free vars
--------------------------------------------------------------------------------

data FV d where
  FV :: String -> FV Infer

instance EqF FV where
  eqF (FV a) (FV b) = if a == b then Just Refl else Nothing

deriving instance Show (FV d)
deriving instance Eq (FV d)

-- type contexts
--------------------------------------------------------------------------------

data Con a where
  Nil  :: Con FV
  Cons :: Type a Infer -> Con a -> Con (Var ((:~:) Infer) a)

lookupVar :: forall a d. Con a -> a d -> TC (Type a Infer)
lookupVar Nil         (FV v) = Left ("Variable: " ++ v ++ " not in context")
lookupVar (Cons t ts) (B b)  = pure (imap F t)
lookupVar (Cons t ts) (F x)  = imap F <$> lookupVar ts x

-- Reduction
--------------------------------------------------------------------------------

-- You can't write this directly, Infer and Check don't let you reduce
nf :: Term a d -> Term a d
nf = undefined

-- Check
--------------------------------------------------------------------------------

-- This ain't works without Value...
-- check :: Con a -> Term a d -> Type a Infer -> TC ()
-- check con t want = case (t, want) of
--   (Lam t, Pi a b) -> check (Cons (nf a) con) (fromScope t) _


-- sugar
--------------------------------------------------------------------------------

instance IsString (Term FV Check) where fromString = Inf . Var . FV
instance IsString (Term FV Infer) where fromString = Var . FV

star      = Inf Star
pi a ty b = Inf (Pi ty (abs1 (FV a) b))
lam a b   = Lam (abs1 (FV a) b)

(==>) :: Type a Check -> Type a Check -> Type a Check
a ==> b = Inf (Pi a (Scope (imap (F . ipure) b)))
infixr 2 ==>

(@@) a b = (App a b)
infixl 8 @@

id' = Ann (lam "a" $ lam "x" $ "x") (pi "a" star $ "a" ==> "a")
ap' = Ann (lam "a" $ lam "b" $ lam "f" $ lam "x" $ Inf $ "f" @@ "x")
          (pi "a" star $ pi "b" star $ ("a" ==> "b") ==> "a" ==> "b")

