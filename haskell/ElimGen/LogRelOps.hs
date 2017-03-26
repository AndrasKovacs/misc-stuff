{-# language
  OverloadedStrings, Strict, LambdaCase, DeriveFunctor,
  DeriveFoldable, TypeFamilies, FlexibleInstances #-}

{-|
  P and R operations for contexts. See bottom of file for examples.
-}

import Control.Arrow
import Data.Foldable
import Data.List
import Data.String

infixl 6 :::

type Name   = String
data List a = Nil | List a ::: a deriving (Functor, Foldable)
type Env    = List (Name, Val)
type Con    = List (Name, Tm)

data Tm
  = Var Name
  | App Tm Tm
  | Pi Name Tm Tm
  | Lam Name Tm
  | U

-- Tm syntactic sugar
-- Use "(x, a) ==> b" for "Pi x a b" and "x ==> b" for "Pi "_" a b"
--------------------------------------------------------------------------------

class PiSugar a where
  (==>) :: a -> Tm -> Tm
  infixr 4 ==>

instance {-# incoherent #-}(a ~ Name, b ~ Tm) => PiSugar (a, b) where
  (x, a) ==> b = Pi x a b

instance (a ~ Tm) => PiSugar a where
  a ==> b = Pi "_" a b

($$) = App
infixl 8 $$

-- β-normalization
--------------------------------------------------------------------------------

data Val
  = VVar Name
  | VApp Val ~Val
  | VPi Name Val (Val -> Val)
  | VLam Name (Val -> Val)
  | VU

evalVar :: Env -> Name -> Val
evalVar Nil             x = VVar x
evalVar (e ::: (x', v)) x = if x == x' then v else evalVar e x

eval :: Env -> Tm -> Val
eval e = \case
  Var x    -> evalVar e x
  App f a  -> case (eval e f, eval e a) of
                (VLam _ t, a) -> t a
                (t       , a) -> VApp t a
  Pi x a b -> VPi x (eval e a) (\a -> eval (e ::: (x, a)) b)
  Lam x t  -> VLam x (\a -> eval (e ::: (x, a)) t)
  U        -> VU

quote :: Val -> Tm
quote = \case
  VVar x    -> Var x
  VApp f a  -> App (quote f) (quote a)
  VPi x a b -> Pi x (quote a) (quote (b (VVar x)))
  VLam x t  -> Lam x (quote (t (VVar x)))
  VU        -> U

class Nf a where nf :: a -> a
instance Nf Tm  where nf = quote . eval Nil
instance Nf Con where nf = fmap (second nf)

-- P-ing
--------------------------------------------------------------------------------

class P a where p :: a -> a

instance P Name where p = (++ "ᴹ")

instance P Tm where
  p = \case
    Var x    -> Var (p x)
    App f a  -> p f $$ a $$ p a
    Pi x a b -> Lam "f'" ((x, a) ==> (p x, p a $$ Var x) ==> p b $$ ("f'" $$ Var x))
    Lam x t  -> Lam x (Lam (p x) (p t))
    U        -> Lam "A" ("A" ==> U)

instance P Con where
  p Nil                = Nil
  p (gamma ::: (x, t)) = p gamma ::: (x, t) ::: (p x, p t $$ Var x)

-- R-ing
--------------------------------------------------------------------------------

data Ix = Zero | One

instance Show Ix where
  show Zero = "₀"
  show One  = "₁"

class R a where
  r   :: a -> a
  sub :: Ix -> a -> a

s0 a = sub Zero a
s1 a = sub One a

instance R Name where
  r = (++ "ᴹ")
  sub i = (++ show i)

instance R Tm where
  r = \case
    Var x    -> Var (r x)
    App f a  -> r f $$ s0 a $$ s1 a $$ r a
    Pi x a b -> Lam "f'₀" $ Lam "f'₁" $
      (s0 x, s0 a) ==>
      (s1 x, s1 a) ==>
      (r x , r a $$ Var (s0 x) $$ Var (s1 x)) ==>
      r b $$ ("f'₀" $$ Var (s0 x)) $$ ("f'₁" $$ Var (s1 x))
    Lam x t -> Lam (s0 x) $ Lam (s1 x) $ r t
    U -> Lam "A₀" $ Lam "A₁" $ "A₀" ==> "A₁" ==> U

  sub i = go [] where
    go bound = \case
      Var x    -> Var (if elem x bound then x else sub i x)
      App f a  -> App (go bound f) (go bound a)
      Pi x a b -> Pi x (go bound a) (go (x:bound) b)
      Lam x t  -> Lam x (go (x:bound) t)
      U        -> U

instance R Con where
  r Nil                = Nil
  r (gamma ::: (x, t)) =
    r gamma ::: (s0 x, s0 t) ::: (s1 x, s1 t) ::: (r x, r t $$ Var (s0 x) $$ Var (s1 x))

  sub i = fmap (\(x, t) -> (sub i x, sub i t))

-- printing
--------------------------------------------------------------------------------

prettyTm :: Int -> Tm -> ShowS
prettyTm prec = go (prec /= 0) where

  unwords' :: [ShowS] -> ShowS
  unwords' = foldr1 (\x acc -> x . (' ':) . acc)

  spine :: Tm -> Tm -> [Tm]
  spine f a = go f [a] where
    go (App f a) args = go f (a : args)
    go t         args = t:args

  lams :: Name -> Tm -> ([Name], Tm)
  lams v t = go [v] t where
    go vs (Lam v t) = go (v:vs) t
    go vs t         = (vs, t)

  freeIn :: Name -> Tm -> Bool
  freeIn x = \case
    Var x'    -> x == x'
    App f a   -> freeIn x f || freeIn x a
    Lam x' t  -> if x == x' then False else freeIn x t
    Pi x' a b -> freeIn x a || if x == x' then False else freeIn x b
    U         -> False

  go :: Bool -> Tm -> ShowS
  go p = \case
    Var x   -> (x++)
    App f a -> showParen p (unwords' $ map (go True) (spine f a))
    Lam x t -> case lams x t of
      (vs, t) -> showParen p (("λ "++) . (unwords (reverse vs)++) . (". "++) . go False t)
    Pi x a b -> showParen p (arg . (" → "++) . go False b)
      where arg = if freeIn x b then showParen True ((x++) . (" : "++) . go False a)
                                else go False a
    U -> ('U':)

instance IsString Tm where fromString = Var
instance Show Tm     where showsPrec  = prettyTm

instance Show Con where
  show = intercalate "\n" . map (\(x, t) -> x ++ " : " ++ show t) . toList

-- Examples.
-- Do not use ' ᴹ ₀ ₁ in inputs, they are reserved.
--------------------------------------------------------------------------------

-- nf $ p nat
-- nf $ r nat
nat = Nil
  ::: ("N", U)
  ::: ("z", "N")
  ::: ("s", ("n", "N") ==> "N")

w = Nil
  ::: ("S", U)
  ::: ("P", ("s", "S") ==> U)
  ::: ("W", U)
  ::: ("sup", ("s", "S") ==> ("f", ("p", "P" $$ "s") ==> "W") ==> "W")

idfun = Nil
  ::: ("IdFun", U)
  ::: ("con", ("f", ("A", U) ==> ("a", "A") ==> "A") ==> "IdFun")

