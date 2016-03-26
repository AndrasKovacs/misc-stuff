
import Control.Monad

data Term
  = Var !Int
  | App Term Term
  | Lam Term Term
  | Pi Term Term
  | Star
  deriving (Eq, Show)

data Val
  = VVar !Int
  | VApp Val Val
  | VLam Type (Val -> Val)
  | VPi  Type (Val -> Val)
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

-- runTC, quote and eval don't really need the whole context
-- I'm passing it along for simplicity right now
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

check :: Cxt -> Term -> Term -> Maybe ()
check cxt t ty = do
  tt <- runTC cxt =<< infer cxt t
  guard $ tt == ty

infer :: Cxt -> Term -> Maybe TC
infer cxt = \case
  Var i   -> pure $ Embed (fst (cxt ! i))
  Star    -> pure $ Embed VStar
  Lam a t -> do
    check cxt a Star
    let a' = eval cxt a
    pure $ TPi a' $ \v -> infer ((a', v) <: cxt) t
  Pi a b -> do
    check cxt a Star
    check (eval cxt a <:: cxt) b Star
    pure $ Embed VStar
  App f x -> do
    infer cxt f >>= \case
      TPi a b -> do
        check cxt x (quote cxt a)
        b (eval cxt x)
      Embed (VPi a b) -> do
        check cxt x (quote cxt a)
        pure $ Embed $ b (eval cxt x)
      _ -> Nothing

infer0 :: Term -> Maybe Term
infer0 = runTC ([], 0) <=< infer ([], 0)

-- HOAS sugar

infer0' :: Val -> Maybe Term
infer0' = runTC ([], 0) <=< infer ([], 0) . quote ([], 0)

lam  = VLam
star = VStar
forAll = lam star

(==>) :: Type -> Type -> Type
a ==> b = VPi a $ const b
infixr 8 ==>

