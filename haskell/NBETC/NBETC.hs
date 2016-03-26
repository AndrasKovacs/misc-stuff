
import Control.Monad
import Text.Show

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

cxt0 :: Cxt
cxt0 = ([], 0)

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
infer0 = runTC cxt0 <=< infer cxt0

-- HOAS sugar
infer0' :: Val -> Maybe Term
infer0' = infer0 . quote cxt0

-- typecheck, then normalize the term
eval0 :: Val -> Maybe Term
eval0 v = quote cxt0 v <$ infer0' v

lam  = VLam
star = VStar
forAll = lam star

(==>) :: Type -> Type -> Type
a ==> b = VPi a $ const b
infixr 8 ==>

id'    = forAll $ \a -> lam a $ \x -> x
const' = forAll $ \a -> forAll $ \b -> lam a $ \x -> lam b $ \_ -> x

compose =
  forAll $ \a ->
  forAll $ \b ->
  forAll $ \c ->
  lam (b ==> c) $ \f ->
  lam (a ==> b) $ \g ->
  lam a $ \x ->
  f $$ (g $$ x)

natTy = VPi star $ \a -> (a ==> a) ==> a ==> a

z = forAll $ \a ->
    lam (a ==> a) $ \s ->
    lam a $ \z ->
    z

s = lam natTy $ \n ->
    forAll $ \a ->
    lam (a ==> a) $ \s ->
    lam a $ \z ->
    s $$ (n $$ a $$ s $$ z)

add =
  lam natTy $ \a ->
  lam natTy $ \b ->
  forAll $ \r ->
  lam (r ==> r) $ \s ->
  lam r $ \z ->
  a $$ r $$ s $$ (b $$ r $$ s $$ z)

mul =
  lam natTy $ \a ->
  lam natTy $ \b ->
  forAll $ \r ->
  lam (r ==> r) $ \s ->
  a $$ r $$ (b $$ r $$ s)

two = s $$ (s $$ z)
five = s $$ (s $$ (s $$ (s $$ (s $$ z))))
ten = add $$ five $$ five
hundred = mul $$ ten $$ ten

nfunTy =
  lam natTy $ \n ->
  n $$ star $$ (lam star $ \t -> star ==> t) $$ star

nfun =
  lam natTy $ \n ->
  lam (nfunTy $$ n) $ \f ->
  star

-- Partial evaluation of type checker ??
data QTC
  = QEmbed Term
  | QTPi Term (Maybe Term)
  deriving (Show)

-- qInfer :: Cxt -> Term -> Maybe QTC
-- qInfer cxt = \case
--   Var i -> pure $ QEmbed (quote cxt (fst (cxt ! i)))
--   Star  -> pure $ QEmbed Star
--   Lam a t -> do
   
    
  -- Var i   -> pure $ Embed (fst (cxt ! i))
  -- Star    -> pure $ Embed VStar
  -- Lam a t -> do
  --   check cxt a Star
  --   let a' = eval cxt a
  --   pure $ TPi a' $ \v -> infer ((a', v) <: cxt) t
  -- Pi a b -> do
  --   check cxt a Star
  --   check (eval cxt a <:: cxt) b Star
  --   pure $ Embed VStar
  -- App f x -> do
  --   infer cxt f >>= \case
  --     TPi a b -> do
  --       check cxt x (quote cxt a)
  --       b (eval cxt x)
  --     Embed (VPi a b) -> do
  --       check cxt x (quote cxt a)
  --       pure $ Embed $ b (eval cxt x)
  --     _ -> Nothing





-- pEval :: Int -> Term -> String -> String
-- pEval d = \case
--   Var i   -> (("v" ++ show i)++)
--   App f x -> pEval d f . (" $$ ("++) . pEval d x . (')':)
--   Lam a t -> let a' = pEval d a in
--     ("lam ("++) . a' . ((") $ \\v" ++ show d ++ " -> ")++) . pEval (d + 1) t
--   Pi  a b -> let a' = pEval d a in
--     ("VPi ("++) . a' . ((") $ \\v" ++ show d ++ " -> ")++) . pEval (d + 1) b
--   Star -> ("VStar"++)

-- pEval0 :: Val -> String
-- pEval0 v = pEval 0 (quote cxt0 v) []
