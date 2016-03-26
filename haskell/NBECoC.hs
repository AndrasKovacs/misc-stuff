
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
  | VLam Val (Val -> Val)
  | VPi  Val (Val -> Val)
  | VStar
 

type Type  = Val
type Type' = [Val] -> Int -> Type
type Val'  = Type'

data Cxt = Cxt {types :: [Type'], vars :: [Val], size :: Int}

peek :: Cxt -> Type' -> Type
peek Cxt{..} val = val vars size

(<:) :: Type' -> Cxt -> Cxt
(<:) ty cxt@Cxt{..} = Cxt (ty : types) (VVar size : vars) (size + 1)

($$) :: Val -> Val -> Val
($$) (VLam _ f) x = f x
($$) f          x = VApp f x
infixl 9 $$

eval :: Term -> Val'
eval (Var i)   env !d = env !! (d - i - 1)
eval Star      _    _ = VStar
eval (App f x) env  d = eval f env d $$ eval x env d
eval (Lam a t) env  d = VLam (eval a env d) $ \v -> eval t (v:env) (d + 1)
eval (Pi  a t) env  d = VPi  (eval a env d) $ \v -> eval t (v:env) (d + 1)

quote :: Cxt -> Val -> Term
quote cxt val = go val (size cxt) where
  go (VVar i)   !d = Var i
  go VStar       d = Star
  go (VApp f x)  d = App (go f d) (go x d)
  go (VLam ty f) d = Lam (go ty d) (go (f (VVar d)) (d + 1))
  go (VPi ty f)  d = Pi  (go ty d) (go (f (VVar d)) (d + 1))

check :: Cxt -> Term -> Type -> Maybe ()
check cxt t ty = do
  tt <- infer cxt t
  guard $ quote cxt (peek cxt tt) == quote cxt ty

infer :: Cxt -> Term -> Maybe Type'
infer cxt@Cxt{..}  = \case  
  Var i ->
    pure $ \env d -> (types !! (d - i - 1)) env d

  Star ->
    pure $ \_ _ -> VStar

  Pi a b -> do
    check cxt a VStar
    let a' = eval a
    check (a' <: cxt) b VStar
    pure $ \_ _ -> VStar
  
  Lam a t -> do
    check cxt a VStar
    let a' = eval a
    b <- infer (a' <: cxt) t
    pure $ \env d -> VPi (a' env d) $ \v -> b (v:env) (d + 1)
    
  App f x -> do
    tf <- infer cxt f
    case peek cxt tf of
      VPi a b -> do
        check cxt x a
        pure $ \env d ->
          case tf env d of VPi _ b -> b (eval x env d)
      _ -> Nothing



cxt0 = Cxt [] [] 0

infer0 :: Term -> Maybe Term
infer0 = fmap (quote cxt0 . peek cxt0) . infer cxt0

id'    = Lam Star $ Lam (Var 0) $ Var 1
const' = Lam Star $ Lam Star $ Lam (Var 0) $ Lam (Var 1) $ Var 2
apId   = Lam (Pi Star (Var 0)) (Var 0)


