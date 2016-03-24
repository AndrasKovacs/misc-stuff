
import Control.Monad
import Debug.Trace

data Term
  = Var !Int
  | App !Term Term
  | Lam Term Term
  | Pi Term Term
  | Star
  deriving (Eq, Show)

data Val
  = VVar !Int
  | VApp !Val Val
  | VLam Type (Val -> Val)
  | VPi  Type (Val -> Val)
  | VStar

type Type = Val

($$) :: Val -> Val -> Val
($$) (VLam _ f) x = f x
($$) f          x = VApp f x
infixl 9 $$

quote :: Val -> Term
quote = flip go 0 where
  go :: Val -> Int -> Term
  go (VVar i)   !d = Var i
  go VStar       d = Star
  go (VApp f x)  d = App (go f d) (go x d)
  go (VLam ty f) d = Lam (go ty d) (go (f (VVar d)) (d + 1))
  go (VPi ty f)  d = Pi  (go ty d) (go (f (VVar d)) (d + 1))

eval :: Term -> [Val] -> Int -> Val
eval = go where
  go :: Term -> [Val] -> Int -> Val
  go (Var i)    env !d = env !! (d - i - 1)
  go Star       env  d = VStar
  go (App f x)  env  d = go f env d $$ go x env d
  go (Lam ty t) env  d = VLam (go ty env d) $ \t' -> go t (t':env) (d + 1)
  go (Pi  ty t) env  d = VPi  (go ty env d) $ \t' -> go t (t':env) (d + 1)

type TC      = Either String
type Closure = [Val] -> Int -> Type
type Cxt     = (Int, [Closure])

(<:) :: Closure -> Cxt -> Cxt
c <: (len, cxt) = (len + 1, c:cxt)

(!) :: Cxt -> Int -> Closure
(!) (_, cxt) i = cxt !! i

cxtLen :: Cxt -> Int
cxtLen = fst

emptyCxt :: Cxt
emptyCxt = (0, [])

check :: Cxt -> Term -> Type -> TC ()
check cxt t want = do
  has <- infer cxt t
  when (quote (has [] (cxtLen cxt)) /= quote want) $ -- is this right?
    Left "type mismatch"

infer :: Cxt -> Term -> TC Closure
infer cxt@(!_, _) t = case t of
  Var i   -> pure (\vs d -> (cxt ! (d - i - 1)) vs d)
  Star    -> pure (\_ _ -> VStar)
  Lam a t -> do
    check cxt a VStar
    let a' = eval a
    b <- infer (a' <: cxt) t
    pure $ \vs d -> VPi (a' vs d) $ \v -> b (v : vs) (d + 1)

infer0 t = (quote . ($0) . ($[])) <$> infer emptyCxt t


-- infer :: [[Val] -> Int -> Type] -> Term -> TC ([Val] -> Int -> Type)
-- infer ts t = case t of
--   Var i   -> pure (\vs d -> (ts !! (d - i - 1)) vs d)
--   Star    -> pure (\_ _ -> Star)
--   Lam a t -> do
--     check ts a Star
--     let a' = eval a
--     b <- infer (a' : ts) t
--     pure $ \vs d -> VPi (a' vs d) $ \v -> b (v : vs) (d + 1)




    -- let a' = eval a vs d
    -- b <- infer (a':ts) (Var d:vs) (d + 1) t

  --   _





-- type TC    = Either String
-- type Cxt a = a -> TC (Type a)

-- consCxt :: Type a -> Cxt a -> Cxt (Var () a)
-- consCxt ty cxt (B ()) = pure (F <$> ty)
-- consCxt ty cxt (F a)  = (F <$>) <$> cxt a

-- check :: Eq a => Cxt a -> Type a -> Term a -> TC ()
-- check cxt want t = do
--   have <- infer cxt t
--   when (have /= want) $ Left "type mismatch"

-- infer :: Eq a => Cxt a -> Term a -> TC (Type a)
-- infer cxt = \case
--   Var a -> cxt a
--   Star  -> pure Star
--   Lam ty t -> do
--     check cxt Star ty
--     let ty' = rnf ty
--     Pi ty' . toScope <$> infer (consCxt ty' cxt) (fromScope t)
--   Pi ty t -> do
--     check cxt Star ty
--     check (consCxt (rnf ty) cxt) Star (fromScope t)
--     pure Star
--   App f x ->
--     infer cxt f >>= \case
--       Pi ty t -> do
--         check cxt ty x
--         pure $ rnf (instantiate1 x t)
--       _ -> Left "can't apply non-function"

-- -- infer in the empty context
-- infer0 :: Eq a => Term a -> TC (Type a)
-- infer0 = infer (const $ Left "variable not in scope")

-- -- smart constructors

-- lam :: Eq a => a -> Type a -> Term a -> Term a
-- lam v ty t = Lam ty (abstract1 v t)

-- pi :: Eq a => a -> Type a -> Term a -> Term a
-- pi v ty t = Pi ty (abstract1 v t)

-- (==>) :: Type a -> Type a -> Type a -- non-dependent function type
-- a ==> b = Pi a (Scope $ fmap (F . pure) b)
-- infixr 5 ==>
