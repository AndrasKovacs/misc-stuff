{-

Disregard this file.

It's just the same as NBECoC3, excep it inferm from Val instead of Term

-}


import Control.Monad
import Debug.Trace

data Term
  = Var !Int
  | App Term Term
  | Lam Term Term
  | Pi Term Term
  | Star
  deriving (Eq, Show)

-- Maybe todo: use Neutral
data Val
  = VVar !Int
  | VApp Val Val
  | VLam Val (Val -> Val)
  | VPi  Val (Val -> Val)
  | VStar

data TC
  = Embed Type
  | TPi Type (Val -> Maybe TC)    

type Type = Val
type Cxt = ([(Type, Val)], Int)

(<:) :: (Type, Val) -> Cxt -> Cxt
(<:) entry (env, d) = (entry:env, d + 1)

(<::) :: Type -> Cxt -> Cxt
(<::) ty (env, d) = ((ty, VVar d):env, d + 1)

(!) :: Cxt -> Int -> (Type, Val)
(!) (env, d) i = env !! (d - i - 1)

($$) :: Val -> Val -> Val
($$) (VLam _ f) x = f x
($$) f          x = VApp f x
infixl 9 $$

--  runTC, quote and eval don't really need the whole context
--  I'm passing it along for simplicity right now
runTC :: Cxt -> TC -> Maybe Term
runTC cxt = \case
  Embed ty -> Just $ quote cxt ty
  TPi a b  -> Pi (quote cxt a) <$> (runTC (a <:: cxt) =<< b (VVar (snd cxt)))

quote :: Cxt -> Val -> Term 
quote cxt = \case
  VVar i   -> Var i
  VApp f x -> App (quote cxt f) (quote cxt x)
  VLam a t -> Lam (quote cxt a) (quote (a <:: cxt) (t (VVar (snd cxt))))
  VPi  a b -> Pi  (quote cxt a) (quote (a <:: cxt) (b (VVar (snd cxt))))
  VStar    -> Star

eval :: Cxt -> Term -> Val
eval cxt = \case
  Var i   -> snd (cxt ! i)
  App f x -> eval cxt f $$ eval cxt x
  Lam a t -> let a' = eval cxt a in VLam a' $ \v -> eval ((a', v) <: cxt) t
  Pi  a b -> let a' = eval cxt a in VPi  a' $ \v -> eval ((a', v) <: cxt) b
  Star    -> VStar                                                    

check :: Cxt -> Val -> Term -> Maybe ()
check cxt t ty = do
  tt <- runTC cxt =<< infer cxt t
  guard $ tt == ty

infer :: Cxt -> Val -> Maybe TC
infer cxt = \case
  VVar i   -> pure $ Embed (fst (cxt ! i))
  VStar    -> pure $ Embed VStar  
  VLam a t -> do
    check cxt a Star
    pure $ TPi a $ \v -> infer ((a, v) <: cxt) (t v)
  VPi a b -> do
    check cxt a Star
    check (a <:: cxt) (b a) Star
    pure $ Embed VStar
  VApp f x -> do
    infer cxt f >>= \case
      TPi a b -> do
        check cxt x (quote cxt a)
        b x
      Embed (VPi a b) -> do
        check cxt x (quote cxt a)
        pure $ Embed $ b a
      _ -> Nothing

infer0 :: Val -> Maybe Term
infer0 = runTC ([], 0) <=< infer ([], 0)

-- HOAS sugar
lam  = VLam
star = VStar
(==>) :: Type -> Type -> Type
a ==> b = VPi a $ const b
infixr 8 ==>

