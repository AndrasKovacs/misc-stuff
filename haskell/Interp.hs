
{-# language Strict, BangPatterns, LambdaCase, CPP, UnicodeSyntax, PatternSynonyms #-}
{-# language DeriveFunctor, DeriveFoldable, MagicHash, UnboxedTuples, ViewPatterns #-}
{-# options_ghc -fwarn-incomplete-patterns #-}

{- | Small interpreter for STG-like language -}

import Prelude hiding (lookup, fix, filter, takeWhile, all, sqrt, mod)
import qualified Prelude as P
import Data.Time.Clock
import System.Environment
import Data.List
import Data.Monoid
import Control.Arrow

import Data.Bits
import Data.Maybe
import GHC.Prim
import GHC.Types
import Debug.Trace

import Data.HashSet (HashSet)
import qualified Data.HashSet as S
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as M

-- Possible TODO-s:
--   smallArray in
--    case branches, constructors, trimmed environments
--   strictness analysis
--   arity annotation in case branch instead of lambdas

--------------------------------------------------------------------------------

data BinOp
  = BOSub
  | BOAdd
  | BOEq
  | BOLte
  | BOLt
  | BOMod
  deriving (Show)

data List' a = Nil' | Cons' a (List' a) deriving (Functor, Foldable)
data List a = Nil | Cons ~a (List a) deriving (Functor, Foldable)

instance Show a => Show (List a) where
  show = show . foldr (:) []

instance Show a => Show (List' a) where
  show = show . foldr (:) []

newtype Env = Env (List Val)

instance Show Env where
  show (Env vs) = show $ map (const "entry") $ foldr (:) [] vs

enil = Env Nil
econs ~v (Env vs) = Env (Cons v vs)
{-# inline econs #-}

data Tm
  = Var Int
  | App Tm Tm
  | Lam Tm
  | Let Tm Tm
  | Case Tm (List' Tm)
  | Con Int (List' Tm)
  | Lit Int
  | BinOp BinOp Tm Tm
  | Trim Int Tm
  | Thunk Int Tm
  | Sqrt Tm
  | Fix Tm
  | Error String
  deriving Show

data Val
  = VCon Int (List Val)
  | VLit Int
  | VLam Env Tm
  deriving Show

vtrue  = VCon 0 Nil
vfalse = VCon 1 Nil

--------------------------------------------------------------------------------

-- type Box a = (# a #)
-- When finished, use (# a #)
data Box a = Box ~a deriving (Show)

varᵉ ∷ Env → Int → Box Val
varᵉ (Env ts) x = go ts x where
  go (Cons t ts) 0 = Box t
  go (Cons t ts) n = go ts (n - 1)
  go _           _ = undefined

trim ∷ Int → Env → Env
trim 0    env = enil
trim (-1) env = env
trim m (Env (Cons v vs)) = case m .&. 1 of
  0 → trim (shiftRA m 1) (Env vs)
  _ → econs v (trim (shiftRA m 1) (Env vs))
trim _ _ = undefined

conᵉ ∷ Env → List' Tm → List Val
conᵉ e = \case
  Nil'       → Nil
  Cons' t ts → let ts' = conᵉ e ts in case t of
      Var x     → let Box t' = varᵉ e x             in Cons t' ts'
      Thunk m t → let e' = trim m e; ~t' = tmᵉ e' t in Cons t' ts'
      _         → let t' = tmᵉ e t                  in Cons t' ts'

casesᵉ ∷ Env → Int → List Val → List' Tm → Val
casesᵉ e 0 ts (Cons' c _) = go e c ts where
  go ∷ Env → Tm → List Val → Val
  go e c       Nil         = tmᵉ e c
  go e (Lam c) (Cons t ts) = go (econs t e) c ts
  go _ _ _ = undefined
casesᵉ e n ts (Cons' _ cs) = casesᵉ e (n - 1) ts cs
casesᵉ _ _ _ _ = undefined

tmᵉ ∷ Env → Tm → Val
tmᵉ e = \case
  Var x        → let Box t = varᵉ e x in t
  Lam t        → VLam e t
  Con c ts     → VCon c (conᵉ e ts)
  Lit n        → VLit n
  Case t cs    → case tmᵉ e t of
                   VCon c ts → casesᵉ e c ts cs
                   _ → undefined
  App (Lam t) u → case u of
                     Var x     → let Box u' = varᵉ e x             in tmᵉ (econs u' e) t
                     Thunk m u → let e' = trim m e; ~u' = tmᵉ e' u in tmᵉ (econs u' e) t
                     _         → let u' = tmᵉ e u                  in tmᵉ (econs u' e) t
  App t u      → case tmᵉ e t of
                   VLam te t → case u of
                     Var x     → let Box u' = varᵉ e x             in tmᵉ (econs u' te) t
                     Thunk m u → let e' = trim m e; ~u' = tmᵉ e' u in tmᵉ (econs u' te) t
                     _         → let u' = tmᵉ e u                  in tmᵉ (econs u' te) t
                   _ → undefined
  Let t u      → case t of
                   Var x     → let Box t' = varᵉ e x             in tmᵉ (econs t' e) u
                   Thunk m t → let e' = trim m e; ~t' = tmᵉ e' t in tmᵉ (econs t' e) u
                   _         → let t' = tmᵉ e t                  in tmᵉ (econs t' e) u
  Thunk m t    → tmᵉ (trim m e) t
  Trim m t     → tmᵉ (trim m e) t
  Fix t        → let t' = tmᵉ (econs t' e) t in t'
  BinOp op t u → case tmᵉ e t of
                   VLit a → case tmᵉ e u of
                     VLit b → case op of
                       BOLt  → if a < b then vtrue else vfalse
                       BOSub → VLit (a - b)
                       BOAdd → VLit (a + b)
                       BOEq  → if a == b then vtrue else vfalse
                       BOLte → if a <= b then vtrue else vfalse
                       BOMod → VLit (P.mod a b)
                     _ → undefined
                   _ → undefined
  Sqrt  t      → case tmᵉ e t of
                   VLit n → VLit (round (P.sqrt (fromIntegral n) ∷ Double))
                   _ → undefined
  Error s      → error s

--------------------------------------------------------------------------------

data RTm
  = RVar String
  | RLam String RTm
  | RTrim [String] RTm
  | RCon Int [RTm]
  | RLet String RTm RTm
  | RLit Int
  | RThunk [String] RTm
  | RFix String RTm
  | RCase RTm [RTm]
  | RApp RTm RTm
  | RBinOp BinOp RTm RTm
  | RSqrt RTm
  | RError String
  deriving Show

removeShadowing ∷ RTm → RTm
removeShadowing = go 0 mempty where
  go ∷ Int → HashMap String String → RTm → RTm
  go i xs = \case
    RVar x   → RVar (xs M.! x)
    RLam x t →
      let x' = if M.member x xs then x ++ show i else x
      in RLam x' (go (i + 1) (M.insert x x' xs) t)
    RCon c ts → RCon c (map (go i xs) ts)
    RLet x t u →
      let x' = if M.member x xs then x ++ show i else x
      in RLet x' (go i xs t) (go (i + 1) (M.insert x x' xs) u)
    RLit n → RLit n
    RFix x t →
      let x' = if M.member x xs then x ++ show i else x
      in RFix x' (go (i + 1) (M.insert x x' xs) t)
    RCase t cs → RCase (go i xs t) (map (go i xs) cs)
    RApp t u → RApp (go i xs t) (go i xs u)
    RBinOp op t u → RBinOp op (go i xs t) (go i xs u)
    RError msg → RError msg
    RSqrt t → RSqrt (go i xs t)
    _ → error "unexpected Trim/Thunk"

-- issue: toTm does not preserve sharing from inlining
trimAndCompact ∷ RTm → RTm
trimAndCompact = fst . go [] where
  goLamFix ∷ [(String, Maybe RTm)] → RTm → (RTm, HashSet String)
  goLamFix e = \case
    RLam x t → case goLamFix ((x, Nothing):e) t of
      (t, S.delete x → xs) → (RLam x t, xs)
    RFix x t → case goLamFix ((x, Nothing):e) t of
      (t, S.delete x → xs) → (RFix x t, xs)
    t → go e t

  goLazy ∷ [(String, Maybe RTm)] → RTm → (RTm, HashSet String)
  goLazy e t = case go e t of
    (t, xs) → case t of
      RCase{}  → (mkThunk e xs t, xs)
      RApp{}   → (mkThunk e xs t, xs)
      RSqrt{}  → (mkThunk e xs t, xs)
      RBinOp{} → (mkThunk e xs t, xs)
      _        → (t, xs)

  mkThunk ∷ [(String, Maybe RTm)] → HashSet String → RTm → RTm
  mkThunk e xs t = RThunk [x | (x, Nothing) ← e, S.member x xs] t

  mkTrim ∷ [(String, Maybe RTm)] → HashSet String → RTm → RTm
  mkTrim e xs t = RTrim [x | (x, Nothing) ← e, S.member x xs] t

  go ∷ [(String, Maybe RTm)] → RTm → (RTm, HashSet String)
  go e = \case
    RVar x   → case fromJust (lookup x e) of
      Nothing → (RVar x, S.singleton x)
      Just t  → (t, mempty)
    RLam x t → case goLamFix ((x, Nothing):e) t of
      (t, S.delete x → xs) → (mkTrim e xs (RLam x t), xs)
    RCon c ts → case unzip (map (goLazy e) ts) of
      (ts, xss) → (RCon c ts, S.unions xss)
    RLet x t u → case go e t of
      (t, txs) →
        case t of
          RTrim [] (RLam{}) → go ((x, Just t):e) u
          _      → case go ((x, Nothing):e) u of
            (u, uxs) → (RLet x t u, S.delete x (S.union txs uxs))
    RFix x t → case goLamFix ((x, Nothing):e) t of
      (t, S.delete x → xs) → (mkTrim e xs (RFix x t), xs)
    RLit n → (RLit n, mempty)
    RCase t ts → case go e t of
      (t, txs) → case unzip (map (goLamFix e) ts) of
        (ts, xss) → (RCase t ts, S.union txs (S.unions xss))
    RApp t u → case go e t of
      (t, txs) → case goLazy e u of
        (u, uxs) → (RApp t u, S.union txs uxs)
    RBinOp op t u → case go e t of
      (t, txs) → case go e u of
        (u, uxs) → (RBinOp op t u, S.union txs uxs)
    RSqrt t → case go e t of (t, xs) → (RSqrt t, xs)
    RError msg → (RError msg, mempty)
    _ → error "unexpected trim/thunk"

fastSetBit ∷ (Num a, Bits a) ⇒ a → Int → a
fastSetBit a i = a .|. unsafeShiftL 1 i
{-# inline fastSetBit #-}

shiftRA ∷ Int → Int → Int
shiftRA (I# n) (I# i) = I# (uncheckedIShiftRA# n i)
{-# inline shiftRA #-}

indexOf ∷ [String] → String → Int
indexOf = go 0 where
  go i []      x = error x
  go i (x':xs) x = if x == x' then i else go (i + 1) xs x

toTrim ∷ [String] → [String] → Int
toTrim = go 0 0 where
  go ∷ Int → Int → [String] → [String] → Int
  go m i (x:[]) (y:[]) =
    if x == y then foldl' fastSetBit m [i..finiteBitSize m - 1]
              else m
  go m i (x:xs) (y:ys) =
    if x == y then go (fastSetBit m i) (i + 1) xs ys
              else go m                (i + 1) xs (y:ys)
  go m i xs [] = m
  go _ _ _ _ = undefined

toTm ∷ RTm → Tm
toTm = go [] where
  go ∷ [String] → RTm → Tm
  go m = \case
    RVar x         → Var (indexOf m x)
    RApp t u       → App (go m t) (go m u)
    RLam x t       → Lam (go (x:m) t)
    RLet x t u     → Let (go m t) (go (x:m) u)
    RFix x t       → Fix (go (x:m) t)
    RLit n         → Lit n
    RCon c args    → Con c (foldr Cons' Nil' $ fmap (go m) args)
    RCase t ts     → Case (go m t) (foldr Cons' Nil' $ fmap (go m) ts)
    RBinOp op t u  → BinOp op (go m t) (go m u)
    RSqrt t        → Sqrt (go m t)
    RError msg     → Error msg
    RTrim xs t     → Trim (toTrim m xs) (go xs t)
    RThunk xs t    → Thunk (toTrim m xs) (go xs t)

compile ∷ RTm → Tm
compile = toTm . trimAndCompact . removeShadowing


-- Embedded sugar
--------------------------------------------------------------------------------

instance Num RTm where
  fromInteger = RLit . fromInteger
  (+)         = RBinOp BOAdd
  (-)         = RBinOp BOSub
  (*)         = undefined
  abs         = undefined
  signum      = undefined

(∙) = RApp
infixl 7 ∙

mkLam ∷ String → (RTm → RTm) → RTm
mkLam x f = RLam x (f (RVar x))

mkLet ∷ String → RTm → (RTm → RTm) → RTm
mkLet x t f = RLet x t (f (RVar x))

mkFix ∷ String → (RTm → RTm) → RTm
mkFix x f = RFix x (f (RVar x))

sqrt   = RSqrt
lte    = RBinOp BOLte
lt     = RBinOp BOLt
primEq = RBinOp BOEq
match  = RCase

#define FIX(x) mkFix "x" $ \x →
#define LAM(x) mkLam "x" $ \x →
#define LET(x, t) mkLet "x" t $ \x →

--------------------------------------------------------------------------------

true      = RCon 0 []
false     = RCon 1 []
nil       = RCon 0 []
cons x xs = RCon 1 [x, xs]
eq        = RBinOp BOEq
mod       = RBinOp BOMod

prog ∷ Int → RTm
prog n =
  LET(filter, (LAM(f) FIX(filter)
    LAM(xs) match xs
       [nil,
        LAM(x) LAM(xs) match (f ∙ x)
          [cons x (filter ∙ xs),
           filter ∙ xs]]))

  LET(takeWhile, (LAM(f) FIX(takeWhile)
    LAM(xs) match xs
      [nil,
       LAM(x) LAM(xs) match (f ∙ x)
         [cons x (takeWhile ∙ xs),
          nil]]))

  LET(fromThen, (LAM(a) FIX(fromThen) LAM(b)
    cons b (fromThen ∙ (a + b))))

  LET(and, (LAM(a) LAM(b) match a [b, false]))
  LET(not, (LAM(b) match b [false, true]))
  LET(or,  (LAM(a) LAM(b) match a [true, b]))

  LET(all, (LAM(f) FIX(all) LAM(xs) match xs
             [true,
               LAM(x) LAM(xs) and ∙ (f ∙ x) ∙ (all ∙ xs)]))

  LET(ix, (FIX(ix) LAM(i) LAM(xs) match xs
               [RError "undefined",
                LAM(x) LAM(xs2)
                  match (primEq i 0)
                      [x,
                       ix ∙ (i - 1) ∙ xs2]]))

  LET(primes, (FIX(primes)
    cons 2 (cons 3 (
      filter ∙ (LAM(n) LET(rt, (sqrt n))
                 all ∙ (LAM(x) not ∙ eq (mod n x) 0) ∙
                       (takeWhile ∙ (LAM(p) or ∙ lt p rt ∙ eq p rt) ∙ primes))
             ∙ (fromThen ∙ 2 ∙ 5)))))

  ix ∙ fromIntegral n ∙ primes

test ∷ RTm
test =
  LET(and, (LAM(a) LAM(b) match a [b, false]))
  LET(all, (LAM(f) FIX(all) LAM(xs) match xs
    [true,
     LAM(x) LAM(xs) and ∙ (f ∙ x) ∙ (all ∙ xs)]))

  all ∙ (LAM(x) true) ∙ cons 0 (cons 4 nil)

leakTest ∷ Int → RTm
leakTest n =
  LET(ix, (FIX(ix) LAM(i) LAM(xs) match xs
               [RError "undefined",
                LAM(x) LAM(xs)
                  match (primEq i 0)
                      [x,
                       (ix ∙ (i - 1) ∙ xs)]]))

  LET(fromThen, (LAM(a) FIX(fromThen)
    LAM(b) cons b (fromThen ∙ (a + b))))

  ix ∙ fromIntegral n ∙ (fromThen ∙ 1 ∙ 0)

--------------------------------------------------------------------------------

timed ∷ IO a → IO a
timed a = do
  t1 ← getCurrentTime
  res ← a
  t2 ← getCurrentTime
  print $ diffUTCTime t2 t1
  pure res

main ∷ IO ()
main = do
  [n] ← getArgs
  timed $ print $ tmᵉ enil $ compile $ prog (read n)
