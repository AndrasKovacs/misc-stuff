import Control.Monad

data Term
  = Var !Int
  | App Term Term
  | Lam Term Term
  | Pi Term Term
  | Star
  deriving (Eq, Show)

-- Consider second Val type without Maybe-s
-- It should be used when we eval a checked term (should be no failure)

-- Or: separate definition for Type values, and term values?
--   -- with possibility of failure only in Type values

-- Type values denote a type checking program instead of a type

data Val
  = VVar !Int
  | VApp Val Val
  | VLam Val (Val -> Maybe Val)
  | VPi  Val (Val -> Maybe Val)
  | VStar

type Type = Val

quote :: [Type] -> [Val] -> Int -> Val -> Maybe Term
quote = undefined

eval :: [Type] -> [Val] -> Int -> Term -> Val
eval = undefined

check :: [Type] -> [Val] -> Int -> Term -> Term -> Maybe ()
check ts vs d t ty = do
  tt <- infer ts vs d t
  guard $ quote ts vs d tt == Just ty

infer :: [Type] -> [Val] -> Int -> Term -> Maybe Type
infer ts vs d = \case
  Var i   -> pure (ts !! (d - i - 1))
  Star    -> pure VStar
  Lam a t -> do
    check ts vs d a Star
    let a' = eval ts vs d a    
    pure $ VPi a' $ \v -> infer (a' : ts) (v : vs) (d + 1) t
  Pi a b -> do
    check ts vs d a Star
    let a' = eval ts vs d a
    check (a':ts) (VVar d:vs) (d + 1) b Star
    pure VStar
  App f x -> do
    tf <- infer ts vs d f
    case tf of
      VPi a b -> do
        a' <- quote ts vs d a
        check ts vs d x a'
        
      _ -> Nothing

      


