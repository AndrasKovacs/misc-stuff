{-# LANGUAGE LambdaCase, DeriveFunctor #-}

import Prelude hiding (pi)
import Control.Applicative
import Control.Monad
import Prelude.Extras
import Bound

data Term a
  = Var a
  | Star
  | Lam (Type a) (Scope () Term a)
  | Pi  (Type a) (Scope () Type a)
  | App (Term a) (Term a)
  deriving (Show, Eq, Functor)

type Type = Term

instance Show1 Term
instance Eq1 Term

instance Applicative Term where
  pure  = return
  (<*>) = ap

instance Monad Term where
  return = Var
  Var a     >>= f = f a
  Star      >>= f = Star
  Lam ty t  >>= f = Lam (ty >>= f) (t >>>= f)
  Pi  ty t  >>= f = Pi  (ty >>= f) (t >>>= f)
  App t1 t2 >>= f = App (t1 >>= f) (t2 >>= f)

rnf :: Term a -> Term a
rnf = \case
  Var a    -> Var a
  Star     -> Star
  Lam ty t -> Lam (rnf ty) (toScope $ rnf $ fromScope t)
  Pi  ty t -> Pi  (rnf ty) (toScope $ rnf $ fromScope t)
  App t1 t2 -> case (rnf t1, rnf t2) of
    (Lam ty t1, t2) -> rnf (instantiate1 t2 t1)
    (f        , x)  -> App f x

type TC    = Either String
type Cxt a = a -> TC (Type a)

consCxt :: Type a -> Cxt a -> Cxt (Var () a)
consCxt ty cxt (B ()) = pure (F <$> ty)
consCxt ty cxt (F a)  = (F <$>) <$> cxt a

check :: Eq a => Cxt a -> Type a -> Term a -> TC ()
check cxt want t = do
  have <- infer cxt t
  when (have /= want) $ Left "type mismatch"

infer :: Eq a => Cxt a -> Term a -> TC (Type a)
infer cxt = \case
  Var a -> cxt a
  Star  -> pure Star
  Lam ty t -> do
    check cxt Star ty
    let ty' = rnf ty
    Pi ty' . toScope <$> infer (consCxt ty' cxt) (fromScope t)
  Pi ty t -> do
    check cxt Star ty
    check (consCxt (rnf ty) cxt) Star (fromScope t)
    pure Star
  App f x ->
    infer cxt f >>= \case
      Pi ty t -> do
        check cxt ty x
        pure $ rnf (instantiate1 x t)
      _ -> Left "can't apply non-function"

-- infer in the empty context
infer0 :: Eq a => Term a -> TC (Type a)
infer0 = infer (const $ Left "variable not in scope")

-- smart constructors

lam :: Eq a => a -> Type a -> Term a -> Term a
lam v ty t = Lam ty (abstract1 v t)

pi :: Eq a => a -> Type a -> Term a -> Term a
pi v ty t = Pi ty (abstract1 v t)

(==>) :: Type a -> Type a -> Type a -- non-dependent function type
a ==> b = Pi a (Scope $ fmap (F . pure) b)
infixr 5 ==>
