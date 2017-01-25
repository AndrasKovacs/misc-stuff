-- | Generating induction motives and methods from telescopes.

{-# language Strict #-}

data Tm
  = Var Int
  | App Tm Tm
  | Lam Tm
  | Pi Tm Tm
  | U

data Val
  = VVar Int
  | VApp Val ~Val
  | VLam (Val -> Val)
  | VPi ~Val (Val -> Val)
  | VU

($$) f x = App f x
infixl 5 $$

(==>) = Pi
infixr 4 ==>

vapp :: Val -> Val -> Val
vapp f ~x = case f of
  VLam f -> f x
  f      -> VApp f x

-- | Evaluate terms with de Bruijn *indices*
eval :: [Val] -> Tm -> Val
eval vs = \case
  Var v   -> vs !! v
  U       -> VU
  App f x -> vapp (eval vs f) (eval vs x)
  Lam t   -> VLam $ \x -> eval (x:vs) t
  Pi a b  -> VPi (eval vs a) $ \x -> eval (x:vs) b

-- | Quote into normal forms with de Bruijn *levels*
quote :: Int -> Val -> Tm
quote d = \case
  VVar v   -> Var v
  VApp f x -> App (quote d f) (quote d x)
  VU       -> U
  VLam f   -> Lam (quote (d + 1) (f (VVar d)))
  VPi a b  -> Pi (quote d a) (quote (d + 1) (b (VVar d)))

nfCon :: [Tm] -> [Tm]
nfCon = snd . foldr go ((0, []), []) where
  go t ((d, vs), con) = ((d + 1, VVar d:vs), quote d (eval vs t) : con)

--------------------------------------------------------------------------------  

-- | Order-preserving embedding
data Emb = Id | Keep Emb | Drop Emb

embVar :: Emb -> Int -> Int
embVar e v = case (e, v) of
  (Id    , v) -> v
  (Drop e, v) -> 1 + embVar e v
  (Keep e, 0) -> 0
  (Keep r, v) -> 1 + embVar r (v - 1)

emb :: Emb -> Tm -> Tm
emb e = \case
  Var v   -> Var (embVar e v)
  App f x -> App (emb e f) (emb e x)
  U       -> U
  Lam t   -> Lam (emb (Keep e) t)
  Pi a b  -> Pi (emb e a) (emb (Keep e) b)

--------------------------------------------------------------------------------

-- | LogPredify contexts.
conP :: [Tm] -> [Tm]
conP = snd . foldr go (Id, []) where
  go t (e, con) = (Drop $ Keep e, (tmP (Drop e) t $$ Var 0): emb e t:con)

-- | LogPredify terms.
tmP :: Emb -> Tm -> Tm
tmP e = \case
  Var v   -> Var (embVar e v - 1)
  App f x -> tmP e f $$ emb e x $$ tmP e x
  U       -> Lam $ Pi (Var 0) U
  Pi a b  -> Lam $ Pi (emb (Drop e) a) $ Pi (tmP (Drop $ Drop e) a $$ Var 0) $
             tmP (Drop $ Keep $ Drop e) b $$ (Var 2 $$ Var 1)
  Lam t   -> Lam $ Lam $ tmP (Drop $ Keep e) t

--------------------------------------------------------------------------------

toDbIx :: Int -> Tm -> Tm
toDbIx d = \case
  Var v   -> Var (d - v - 1)
  App f x -> App (toDbIx d f) (toDbIx d x)
  U       -> U
  Pi a b  -> Pi (toDbIx d a) (toDbIx (d + 1) b)
  Lam t   -> Lam (toDbIx (d + 1) t)

toDbIxCon :: [Tm] -> [Tm]
toDbIxCon = snd . foldr (\t (d, con) -> (d + 1, toDbIx d t:con)) (0, [])
  
--------------------------------------------------------------------------------

prettyTm :: Int -> Tm -> ShowS
prettyTm prec = go (prec /= 0) where

  unwords' :: [ShowS] -> ShowS
  unwords' = foldr1 (\x acc -> x . (' ':) . acc)

  spine :: Tm -> Tm -> [Tm]
  spine f x = go f [x] where
    go (App f y) args = go f (y : args)
    go t         args = t:args

  go :: Bool -> Tm -> ShowS
  go p = \case
    Var i   -> (show i++)
    App f x -> showParen p (unwords' $ map (go True) (spine f x))
    Lam   t -> showParen p (("\\. "++) . go False t)
    U       -> ('U':)
    Pi a b  -> showParen p (go True a . (" -> "++) . go False b)

instance Show Tm where
  showsPrec = prettyTm

instance Num Tm where
  fromInteger = Var . fromIntegral
  (+) = undefined; (*) = undefined; abs = undefined; signum = undefined; (-) = undefined

--------------------------------------------------------------------------------

-- | LogPred-ify a context and print it. The input is given with de Bruijn levels,
--   in left-to-right dependency order.
conP' :: [Tm] -> IO ()
conP' = mapM_ print . zip [0..] . reverse . nfCon . conP . toDbIxCon . reverse

--------------------------------------------------------------------------------

nat  = [U, 0, 0 ==> 0]
bool = [U, 0, 0]

-- nested list
-- data List a = Nil | Cons a (List (List a))
nlist = [U ==> U, U ==> 0 $$ 1, U ==> 2 ==> (0 $$ (0 $$ 2)) ==> (0 $$ 2)]
--       0        1             2     3             

{-
nlist : U -> U
nil   : (A : U) -> nlist A
cons  : (A : U) -> A -> nlist (nlist A) -> nlist A

nlist* : (A : U) -> (A -> U) -> nlist A -> U
nil*   : (A : U) -> (A* : A -> U) -> nlist* A A* (nil A)
cons*  :
     (A : U) -> (A* : A -> U)
  -> (a : A) -> (a* : A* a)
  -> (as : nlist (nlist A))
  -> (as* : nlist* (nlist A) (nlist* A A*) as)
  -> nlist* A A* (cons A a as)
------------------------------------------------------------
-> (A : U) -> (A* : A -> U) -> (as : nlist A) -> nlist* A A* as

-- Not very usable eliminator for nlist!
-- We can't even write the following:

-- f : nlist Nat -> nlist Nat
-- f (nil _)       = nil _
-- f (cons _ x xs) = cons _ (suc x) xs
-}


{-
A : Type
--------------------------------------------------------------------------------
list : Type
nil : list
cons : A -> list -> list

list* : list -> Type
nil*  : list* nil
cons* : (a : A)(as : list) -> list* as -> list* (cons a as)

-}



