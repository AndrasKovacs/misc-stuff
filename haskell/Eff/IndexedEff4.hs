
{-|
Atkey style indexed extensible effects. Also, we have an open sum of effects that is
indexed by the heterogeneous list of all the indices in the component effects.
-}

{-# language
  UndecidableInstances, TypeInType, TypeApplications,
  AllowAmbiguousTypes, GADTs, TypeFamilies, ScopedTypeVariables,
  UndecidableInstances, LambdaCase, EmptyCase, TypeOperators, ConstraintKinds,
  NoMonomorphismRestriction, FlexibleContexts, MultiParamTypeClasses,
  FlexibleInstances #-}

{-# options_ghc -Wno-partial-type-signatures #-}

import Prelude hiding (read)

import Control.Monad.Indexed
import Data.Kind
import GHC.Exts
import Data.Singletons.Prelude hiding (Elem, (:>))
import System.IO

(>>>) :: IxApplicative m => m i j a -> m j k b -> m i k b
f >>> g = imap (const id) f `iap` g

infixl 1 >>>

-- FastTCQueue reimplementation, because we need to index with arbitrary kinds,
-- not just *. Also specialized to Atkey's indexed types, so we have
-- slightly less confusion with the implementation.
--------------------------------------------------------------------------------  

data FTCQueue f i j a b where
  Leaf :: (a -> f i j b) -> FTCQueue f i j a b
  Node :: FTCQueue f i j a b -> FTCQueue f j k b c -> FTCQueue f i k a c

(|>) :: FTCQueue f i j a b -> (b -> f j k c)  -> FTCQueue f i k a c
t |> r = Node t (Leaf r)

(><) :: FTCQueue f i j a b -> FTCQueue f j k b c -> FTCQueue f i k a c
l >< r = Node l r

data ViewL f i j a b where
  TOne  :: (a -> f i j b) -> ViewL f i j a b
  (:|)  :: (a -> f i j b) -> FTCQueue f j k b c  -> ViewL f i k a c

viewl :: FTCQueue f i j a b -> ViewL f i j a b
viewl (Leaf f)   = TOne f
viewl (Node l r) = go l r
 where
   go :: FTCQueue f i j a b -> FTCQueue f j k b c -> ViewL f i k a c
   go (Leaf r)   t = r :| t
   go (Node l r) t = go l (Node r t)

-- Sums
--------------------------------------------------------------------------------

type Ixed k = k -> k -> * -> *

-- A heterogeneously indexed list for the functors
data IxNP :: [*] -> * where
  INil  :: IxNP '[]
  (:::) :: Ixed k -> IxNP ks -> IxNP (k ': ks)
infixr 5 :::

-- A heterogeneous list for the indices  
data HList :: [*] -> * where
  Nil  :: HList '[]
  (:>) :: a -> HList as -> HList (a ': as)
infixr 5 :>  

-- with implicit ks argument
data Sum :: forall ks. IxNP ks -> Ixed (HList ks) where
  Here  :: f i j a -> Sum (f ::: fs) (i :> is) (j :> is) a
  There :: Sum fs is js a  -> Sum (f ::: fs) (i :> is) (i :> js) a

-- Generic lifted list search
--------------------------------------------------------------------------------

data Nat = Z | S Nat   

data Entry = App | forall a. Con a

type family (xs :: [a]) ++ (ys :: [a]) :: [a] where
  '[]       ++ ys = ys
  (x ': xs) ++ ys = x ': (xs ++ ys)

type family Preord (x :: a) :: [Entry] where
  Preord (f x) = App ': (Preord f ++ Preord x)
  Preord x     = '[ Con x]

type family (x :: a) == (y :: b) :: Bool where
  x == x = True
  _ == _ = False

type family PreordList (xs :: [a]) (i :: Nat) :: [(Nat, [Entry])] where
  PreordList '[]       _ = '[]
  PreordList (a ': as) i = '(i, Preord a) ': PreordList as (S i)

type family Narrow (e :: Entry) (xs :: [(Nat, [Entry])]) :: [(Nat, [Entry])] where
  Narrow _ '[]                     = '[]
  Narrow e ('(i, e' ': es) ': ess) = If (e == e') '[ '(i, es)] '[] ++ Narrow e ess

type family Find_ (es :: [Entry]) (ess :: [(Nat, [Entry])]) :: Nat where
  Find_ _        '[ '(i, _)] = i
  Find_ (e ': es) ess        = Find_ es (Narrow e ess)

type Find x ys = Find_ (Preord x) (PreordList ys Z)

-- Functions to search for effects in the context.
--------------------------------------------------------------------------------

-- Only search in effects; we could search in indices too but
-- testing shows that it rarely works well, and moreover we should
-- label effects anyway if there is more than one effect of
-- the same type.
data Bundled :: * where
  Bundled :: forall k. Ixed k -> Bundled

type family Bundle (fs :: IxNP ks) :: [Bundled] where
  Bundle INil       = '[]
  Bundle (f ::: fs) = ('Bundled f ': Bundle fs)

type FindEff f fs = Find ('Bundled f) (Bundle fs)

-- Inj/prj
--------------------------------------------------------------------------------

class Elem' (n :: Nat) (f :: Ixed k) i o (fs :: IxNP ks) is os where
  inj' :: forall a. f i o a -> Sum fs is os a
  prj' :: forall a. Sum fs is os a -> Maybe (f i o a)
  
instance (fs ~~ (f ::: fs'), is ~~ (i :> is'), os ~~ (o :> is')) =>
  Elem' Z f i o fs is os where
  inj'          = Here
  prj' (Here f) = Just f
  prj' _        = Nothing

instance
  (Elem' n f i o fs' is' os', fs ~~ (f' ::: fs'), is ~~ (i' :> is'), os ~~ (i' :> os')) =>
  Elem' (S n) f i o fs is os where
  inj'            = There . inj' @n
  prj' (Here _)   = Nothing
  prj' (There ns) = prj' @n ns

type Elem f i o fs is os = Elem' (FindEff f fs) f i o fs is os

-- Extensible effects
--------------------------------------------------------------------------------

ftcApp :: FTCQueue (Eff fs) i o a b -> a -> Eff fs i o b
ftcApp f a = case viewl f of
  TOne k -> k a
  k :| t -> case k a of
    Pure a       -> ftcApp t a
    Impure cmd k -> Impure cmd (k >< t)    

data Eff :: forall ks. IxNP ks -> Ixed (HList ks) where
  Pure   :: a -> Eff fs is is a
  Impure :: Sum fs is os a -> FTCQueue (Eff fs) os ks a b -> Eff fs is ks b

instance IxFunctor (Eff fs) where
  imap f (Pure a)     = Pure (f a)
  imap f (Impure a g) = Impure a (g |> (Pure . f))
  
instance IxPointed (Eff fs) where
  ireturn = Pure
  
instance IxApplicative (Eff fs) where
  iap (Pure f)     a  = imap (f $) a
  iap (Impure a f) m  = Impure a (f |> (`imap` m))
  
instance IxMonad (Eff fs) where
  ibind f (Pure a)     = f a
  ibind f (Impure a g) = Impure a (g |> f)

send ::
  forall f i o fs is os a.
  Elem f i o fs is os => f i o a -> Eff fs is os a
send f = Impure (inj' @(FindEff f fs) f) (Leaf Pure)

run :: Eff INil Nil Nil a -> a
run (Pure a) = a

-- Indexed labelled state
--------------------------------------------------------------------------------

data State :: Symbol -> Ixed * where
  Get :: State name i i i
  Put :: o -> State name i o ()

get ::
  forall name i o fs is os.  
  Elem (State name) i i fs is os => Eff fs is os i
get = send (Get @name)

put ::
  forall name i o fs is os.
  Elem (State name) i o fs is os => o -> Eff fs is os ()
put o = send (Put @name @i o)

runState ::
  forall name i o fs is os a.
  i -> Eff (State name ::: fs) (i :> is) (o :> os) a -> Eff fs is os (a, o)
runState i (Pure a)                  = Pure (a, i)
runState i (Impure (Here Get)     k) = runState i (ftcApp k i)
runState i (Impure (Here (Put o)) k) = runState o (ftcApp k ())
runState i (Impure (There cmd)    k) = Impure cmd (Leaf $ runState i . ftcApp k)

-- Named file operations
--------------------------------------------------------------------------------

data FileStatus = FOpen | FClosed

data File (name :: Symbol) i o a where
  Open  ::           File name FClosed FOpen   ()
  Close ::           File name FOpen   FClosed ()
  Read  ::           File name FOpen   FOpen   String
  Write :: String -> File name FOpen   FOpen   ()

open ::
  forall name fs is os.
  Elem (File name) FClosed FOpen fs is os => Eff fs is os ()
open = send (Open @name)

close ::
  forall name fs is os.
  Elem (File name) FOpen FClosed fs is os => Eff fs is os ()
close = send (Close @name)

write ::
  forall name fs is os.
  (SingI name, Elem (File name) FOpen FOpen fs is os) => String -> Eff fs is os ()
write str = send (Write @name str)

read ::
  forall name fs is os.
  (SingI name, Elem (File name) FOpen FOpen fs is os) => Eff fs is os String
read = send (Read @name)


--------------------------------------------------------------------------------


-- runFileC ::
--   forall name a o.
--   SingI name => Eff (File name ::: INil) (FClosed :> Nil) (o :> Nil) a -> IO a
-- runFileC (Pure a) = pure a
-- runFileC (Impure (Here Open) k) = do
--     h <- openFile (fromSing (sing @_ @name)) ReadWriteMode
--     runFileO h (ftcApp k ())
    
-- runFileO ::
--   forall name a o. SingI name =>
--   Handle -> Eff (File name ::: INil) (FOpen :> Nil) (o :> Nil) a -> IO a
-- runFileO h (Pure a) = pure a
-- runFileO h (Impure (Here cmd) k) = case cmd of
--  Close     -> hClose h >> runFileC (ftcApp k ())
--  Read      -> do {l <- hGetLine h; runFileO h (ftcApp k l)}
--  Write str -> hPutStrLn h str >> runFileO h (ftcApp k ())

-- runFile :: forall name a.
--   SingI name => Eff (File name ::: INil) (FClosed :> Nil) (FClosed :> Nil) a -> IO a
-- runFile = runFileC

--------------------------------------------------------------------------------

-- File to State
    
runFileC ::
  forall name a o.
  SingI name => Eff (File name ::: INil) (FClosed :> Nil) (o :> Nil) a -> IO a
runFileC (Pure a) = pure a
runFileC (Impure (Here Open) k) = do
    h <- openFile (fromSing (sing @_ @name)) ReadWriteMode
    runFileO h (ftcApp k ())
    
runFileO ::
  forall name a o. SingI name =>
  Handle -> Eff (File name ::: INil) (FOpen :> Nil) (o :> Nil) a -> IO a
runFileO h (Pure a) = pure a
runFileO h (Impure (Here cmd) k) = case cmd of
 Close     -> hClose h >> runFileC (ftcApp k ())
 Read      -> do {l <- hGetLine h; runFileO h (ftcApp k l)}
 Write str -> hPutStrLn h str >> runFileO h (ftcApp k ())

runFile :: forall name a.
  SingI name => Eff (File name ::: INil) (FClosed :> Nil) (FClosed :> Nil) a -> IO a
runFile = runFileC
            


-- Example
--------------------------------------------------------------------------------

-- We have a labelled indexed state and two labelled file handles
-- Input indices in the first line, outputs in the second.
test :: Eff
  (State "x" ::: File "foo"    ::: File "bar" ::: INil)
  (Int       :>  FClosed       :>  FOpen      :>  Nil )
  (String    :>  FOpen         :>  FClosed    :>  Nil )
  ()
test = 
  get >>>= \x -> 
  put (x + 100) >>>
  open @"foo"   >>>
  close @"bar"  >>>
  put "I have to put here some string" >>>
  ireturn ()


  

