{-# LANGUAGE LambdaCase, DeriveFunctor #-}

module BoundDependentLC where

{- TODO:
   - make Cxt first-order GADT
   - parser

   - error messages:
     - src pos
     - original names carried by bound vars
     - pretty printing eta-short normal forms

   - representations:
     - front:
         with all the sugar and src pos
     - desugared:
         with src pos, implicits + annotations, TC elaborates to core
     - core:
         No implicits, no src pos, decorated (but not annotated) with some types
         purepose: easy TC and checking for def. equality
         optionally: coreValue:
            - NBE for core with beta/eta normalization
            - May be used during elab.
     - value:
         NBE, types and annotations erased
         used for interpreted running

  - Faster, more flexible Bound, fast context with strongly typed API
    - Should be enough for "top-level" names for now
    - sane hereditary subst
      - investigate NBE too

  - fixpoints, dependent case, inductive data
    - termination checking

  - holes
-}


import Prelude hiding (pi)
import Control.Applicative
import Control.Monad
import Prelude.Extras
import Bound

data Term a
  = Var a
  | Star
  | Lam (Maybe (Type a)) (Scope () Term a)
  | Pi  (Type a) (Scope () Type a)
  | App (Term a) (Term a)
  | Ann (Term a) (Type a)
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
  Lam ty t  >>= f = Lam ((f =<<) <$> ty) (t >>>= f)
  Pi  ty t  >>= f = Pi  (f =<< ty) (t >>>= f)
  App t1 t2 >>= f = App (t1 >>= f) (t2 >>= f)
  Ann t ty  >>= f = Ann (t >>= f) (ty >>= f)

type TC = Either String

type Cxt a = a -> TC (Type a)

-- Context extension.
(<:) :: Type a -> Cxt a -> Cxt (Var () a) 
(<:) ty cxt (B ()) = pure (F <$> ty)
(<:) ty cxt (F a)  = (F <$>) <$> cxt a
infixr 5 <:

-- Eta reduce term. 
etaReduce :: Eq a => Term a -> Term a
etaReduce = undefined

-- Eta expand variable.
etaExpand :: Eq a => Type a -> a -> Term a
etaExpand (Pi a b) v = _ -- this ain't simple
  -- Lam Nothing (Scope (App (Var (F (Var v))) (Var (B ()))))

-- Reduce term to eta-beta nf. Also remove annotations from terms and lambda args.
rnf :: Eq a => Cxt a -> Type a -> Term a -> Term a
rnf cxt ty = \case
  Var a   -> etaExpand ty a
  Star    -> Star
  Ann t _ -> rnf cxt ty t
  Lam _ t -> case ty of
    Pi a b -> Lam Nothing (toScope $ rnf (a <: cxt) (fromScope b) (fromScope t))
    _      -> error "impossible: type mismatch on rnf"
  Pi a b  -> Pi (rnf cxt Star a) (toScope $ rnf (a <: cxt) Star $ fromScope b)
  App f x -> case (infer cxt f, infer cxt x) of
    (Right tf, Right tx) -> case (rnf cxt tf f, rnf cxt tx x) of
      (Lam _ t, x') -> rnf cxt ty (instantiate1 x' t)
      (f'     , x') -> App f' x'
    _ -> error "impossible: type error in rnf"        
            
-- Check type of term, return term in nf.
checkNf :: Eq a => Cxt a -> Type a -> Term a -> TC (Term a)
checkNf cxt ty t = rnf cxt ty t <$ check cxt ty t

-- Check type.
check :: Eq a => Cxt a -> Type a -> Term a -> TC ()
check cxt ty = \case
  Lam Nothing t -> case ty of
    Pi a b -> check (a <: cxt) (fromScope b) (fromScope t)
    _      -> Left "type mismatch"
  t -> do
    ty' <- infer cxt t
    when (ty /= ty') $ Left "type mismatch"    

-- Infer type and return it in nf.
infer :: Eq a => Cxt a -> Term a -> TC (Type a)
infer cxt = \case
  Var a -> cxt a
  Star  -> pure Star
  Ann t ty -> do
    ty' <- checkNf cxt Star ty
    check cxt ty' t
    pure ty'
  Lam (Just ty) t -> do
    ty' <- checkNf cxt Star ty
    Pi ty' . toScope <$> infer (ty' <: cxt) (fromScope t)
  Lam Nothing _ ->
    Left "Can't infer type for unannotated lambda binding"
  Pi a b -> do
    a' <- checkNf cxt Star a
    check (a' <: cxt) Star (fromScope b)
    pure Star
  App f x -> do
    (a, b) <- case f of
      Lam Nothing t -> do
        a <- infer cxt x
        b <- toScope <$> infer (a <: cxt) (fromScope t)
        pure (a, b)
      _ -> infer cxt f >>= \case
        Pi a b -> pure (a, b)
        _      -> Left "can't apply non-function"
    pure $ rnf cxt Star (instantiate1 x b)

-- infer in the empty context
infer0 :: Eq a => Term a -> TC (Type a)
infer0 = infer (const $ Left "variable not in scope")

-- smart constructors

lam :: Eq a => a -> Type a -> Term a -> Term a
lam v ty t = Lam (Just ty) (abstract1 v t)

lam' :: Eq a => a -> Term a -> Term a
lam' v t = Lam Nothing (abstract1 v t)

pi :: Eq a => a -> Type a -> Term a -> Term a
pi v ty t = Pi ty (abstract1 v t)

(@@) :: Term a -> Term a -> Term a
(@@) = App
infixl 9 @@

(==>) :: Type a -> Type a -> Type a -- non-dependent function type
a ==> b = Pi a (Scope $ fmap (F . pure) b)
infixr 5 ==>

natTy = pi "r" Star $ (Var "r" ==> Var "r") ==> Var "r" ==> Var "r"
z = lam "r" Star $ lam "s" (Var "r" ==> Var "r") $ lam "z" (Var "r") $ Var "z"
-- -- s = lam "n" natTy $
-- --     pi "r" Star $ lam "s" (Var "r" ==> Var "r") $ lam "z" Star $

