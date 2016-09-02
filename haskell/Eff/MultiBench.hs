{-# language FlexibleContexts, BangPatterns, TypeApplications, GADTs, TypeFamilies,
    NoMonoLocalBinds, GeneralizedNewtypeDeriving, DeriveFunctor,
    DataKinds, NoMonomorphismRestriction, LambdaCase #-}

-- | Benchmarks for various effect system implementations

import Control.Monad
import Data.Monoid
import Criterion.Main
import System.Random

import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Writer.Strict
import Control.Monad.Except
import Control.Monad.Identity

import qualified MultiBenchModule as Mod

import qualified Control.Monad.Freer as F
import qualified Control.Monad.Freer.State as F
import qualified Control.Monad.Freer.Reader as F
import qualified Control.Monad.Freer.Writer as F
import qualified Control.Monad.Freer.Exception as F
import qualified Control.Monad.Freer.Internal as F
import qualified Data.Open.Union as F

import qualified Control.Eff as E
import qualified Control.Eff.State.Strict as E
import qualified Control.Eff.Reader.Strict as E
import qualified Control.Eff.Writer.Strict as E
import qualified Control.Eff.Exception as E

import qualified EffInference as I
import qualified FreeState as FS


times :: Monad m => Int -> m a -> m ()
times n ma = go n where
  go 0 = pure ()
  go n = ma >> go (n - 1)
{-# inline times #-}


-- Use only state, lift variable number of effects over/under
--------------------------------------------------------------------------------

test1mtl :: MonadState Int m => Int -> m Int
test1mtl n = foldM f 1 [0..n] where
  f acc x | x `rem` 5 == 0 = do
              s <- get
              put $! (s + 1)
              pure $! max acc x
          | otherwise = pure $! max acc x

test1F :: F.Member (F.State Int) fs => Int -> F.Eff fs Int
test1F n = foldM f 1 [0..n] where
  f acc x | x `rem` 5 == 0 = do
              s <- F.get @Int
              F.put $! (s + 1)
              pure $! max acc x
          | otherwise = pure $! max acc x

test1E :: E.Member (E.State Int) fs => Int -> E.Eff fs Int
test1E n = foldM f 1 [0..n] where
  f acc x | x `rem` 5 == 0 = do
              s <- E.get @Int
              E.put $! (s + 1)
              pure $! max acc x
          | otherwise = pure $! max acc x

test1I :: I.Elem (I.State Int) fs => Int -> I.Eff fs Int
test1I n = foldM f 1 [0..n] where
  f acc x | x `rem` 5 == 0 = do
              s <- I.get @Int
              I.put $! (s + 1)
              pure $! max acc x
          | otherwise = pure $! max acc x

-- Monomorphic stack that uses all effects
--------------------------------------------------------------------------------

test2mtl :: Int -> StateT Int (ReaderT Int (StateT Bool (Reader Bool))) ()
test2mtl n = replicateM_ n $ do
  rint  <- lift $ ask
  rbool <- lift $ lift $ lift ask
  modify' $ \n -> if n < rint && rbool then n + 10 else n + 20
  lift $ lift $ modify' $ \b -> if b then b && rbool else rint < 20

test2F :: Int -> F.Eff [F.State Int, F.Reader Int, F.State Bool, F.Reader Bool] ()
test2F n = replicateM_ n $ do
  rint <- F.ask @Int
  rbool <- F.ask @Bool
  F.modify @Int $ \n -> if n < rint && rbool then n + 10 else n + 20
  F.modify @Bool $ \b -> if b then b && rbool else rint < 20


-- Manually fused handler for monomorphic Freer stack
--------------------------------------------------------------------------------

bigHandler ::
  Int -> Int -> Bool -> Bool
  -> F.Eff [F.State Int, F.Reader Int, F.State Bool, F.Reader Bool] ()
  -> (((), Int), Bool)
bigHandler si ri sb rb = F.run . go si sb where
  go :: Int -> Bool
        -> F.Eff [F.State Int, F.Reader Int, F.State Bool, F.Reader Bool] ()
        -> F.Eff '[] (((), Int), Bool)
  go si sb (F.Val a) = F.Val (((), si), sb)
  go si sb (F.E c k) = case c of
    F.UNow F.Get                                  -> go si  sb  (F.qApp k si)
    F.UNow (F.Put si')                            -> go si' sb  (F.qApp k ())
    F.UNext (F.UNow F.Reader)                     -> go si  sb  (F.qApp k ri)
    F.UNext (F.UNext (F.UNow F.Get))              -> go si  sb  (F.qApp k sb)
    F.UNext (F.UNext (F.UNow (F.Put sb')))        -> go si  sb' (F.qApp k ())
    F.UNext (F.UNext (F.UNext (F.UNow F.Reader))) -> go si  sb  (F.qApp k rb)


--------------------------------------------------------------------------------


main = do

  -- Used to definitively disable bench argument inlining
  !n <- randomRIO (1000000, 1000000) :: IO Int
  !m <- randomRIO (0, 0) :: IO Int

  let runRT = (`runReaderT`  (m :: Int))
  let runR  = (`runReader`   (m :: Int))
  let runST = (`runStateT`   (m :: Int))
  let runS  = (`runState`    (m :: Int))
  let runWT = runWriterT @(Sum Int)
  let runW  = runWriter  @(Sum Int)

  let runRF = (`F.runReader` (m :: Int))
  let runSF = (`F.runState`  (m :: Int))
  let runWF = F.runWriter @(Sum Int)

  let runRI = I.runReader (m :: Int)
  let runSI = I.runState  (m :: Int)
  let runWI = I.runWriter @(Sum Int)

  let runRE = (`E.runReader` (m :: Int))
  let runSE = (E.runState (m :: Int))
  let runWE = E.runWriter @Int (+) 0

  defaultMain [

    -- Specialization always seem to work, but with only inlinable
    -- we don't get unboxing (which matters hugely for Int operations,
    -- not so much for less "numeric" data)
    bgroup "mtlSpec" [
      bgroup "no_inline" [
        bench "RRRRS" $ whnf (runR . runRT . runRT . runRT . runST . Mod.test1mtl) n
        ],
      bgroup "inlinable" [
        bench "RRRRS" $ whnf (runR . runRT . runRT . runRT . runST . Mod.test1mtl_inlinable) n
        ],
      bgroup "inline" [
        bench "RRRRS" $ whnf (runR . runRT . runRT . runRT . runST . Mod.test1mtl_inline) n
        ],
      bgroup "home module" [
        bench "RRRRS" $ whnf (runR . runRT . runRT . runRT . runST . test1mtl) n
        ]
      ]

    -- bgroup "test1" [
    -- -- literally no overhead, no slowdown for large stack
    --   bgroup "MTL" [
    --     bench "SR"    $ whnf (runS . runRT . test1mtl) n,
    --     bench "SRR"   $ whnf (runS . runRT . runRT . test1mtl) n,
    --     bench "SRRR"  $ whnf (runS . runRT . runRT . runRT . test1mtl) n,
    --     bench "SRRRR" $ whnf (runS . runRT . runRT . runRT . runRT . test1mtl) n,
    --     bench "RS"    $ whnf (runR . runST . test1mtl) n,
    --     bench "RRS"   $ whnf (runR . runRT . runST . test1mtl) n,
    --     bench "RRRS"  $ whnf (runR . runRT . runRT . runST . test1mtl) n,
    --     bench "RRRRS" $ whnf (runR . runRT . runRT . runRT . runST . test1mtl) n,
    --     bench "S"     $ whnf (runS . test1mtl) n
    --     ],

    --   -- Freer slower than mtl by about 10x, but doesn't slow much for large stack
    --   bgroup "Freer" [
    --     bench "SR"    $ nf (F.run . runSF . runRF . test1F) n,
    --     bench "SRR"   $ nf (F.run . runSF . runRF . runRF . test1F) n,
    --     bench "SRRR"  $ nf (F.run . runSF . runRF . runRF . runRF . test1F) n,
    --     bench "SRRRR" $ nf (F.run . runSF . runRF . runRF . runRF . runRF . test1F) n,
    --     bench "RS"    $ nf (F.run . runRF . runSF . test1F) n,
    --     bench "RRS"   $ nf (F.run . runRF . runRF . runSF . test1F) n,
    --     bench "RRRS"  $ nf (F.run . runRF . runRF . runRF . runSF . test1F) n,
    --     bench "RRRRS" $ nf (F.run . runRF . runRF . runRF . runRF . runSF . test1F) n,
    --     bench "S"     $ nf (F.run . runSF . test1F) n
    --     ],

    --   -- Freer faster than plain old Free monad Eff!
    --   bgroup "EffInference" [
    --     bench "SR"    $ nf (I.run . runSI . runRI . test1I) n,
    --     bench "SRR"   $ nf (I.run . runSI . runRI . runRI . test1I) n,
    --     bench "SRRR"  $ nf (I.run . runSI . runRI . runRI . runRI . test1I) n,
    --     bench "SRRRR" $ nf (I.run . runSI . runRI . runRI . runRI . runRI . test1I) n,
    --     bench "RS"    $ nf (I.run . runRI . runSI . test1I) n,
    --     bench "RRS"   $ nf (I.run . runRI . runRI . runSI . test1I) n,
    --     bench "RRRS"  $ nf (I.run . runRI . runRI . runRI . runSI . test1I) n,
    --     bench "RRRRS" $ nf (I.run . runRI . runRI . runRI . runRI . runSI . test1I) n,
    --     bench "S"     $ nf (I.run . runSI . test1I) n
    --     ],

    --   -- Slow as hell, clearly subsumed by Freer
    --   bgroup "Eff" [
    --     bench "SR"    $ nf (E.run . runSE . runRE . test1E) n,
    --     bench "SRR"   $ nf (E.run . runSE . runRE . runRE . test1E) n,
    --     bench "SRRR"  $ nf (E.run . runSE . runRE . runRE . runRE . test1E) n,
    --     bench "SRRRR" $ nf (E.run . runSE . runRE . runRE . runRE . runRE . test1E) n,
    --     bench "RS"    $ nf (E.run . runRE . runSE . test1E) n,
    --     bench "RRS"   $ nf (E.run . runRE . runRE . runSE . test1E) n,
    --     bench "RRRS"  $ nf (E.run . runRE . runRE . runRE . runSE . test1E) n,
    --     bench "RRRRS" $ nf (E.run . runRE . runRE . runRE . runRE . runSE . test1E) n,
    --     bench "S"     $ nf (E.run . runSE . test1E) n
    --     ]
    --   ],

    -- bgroup "Count" [
    --   bgroup "Freer" [
    --       bench "Count" $ nf (\n -> F.run $ runSF $ times n $ F.modify @Int (+1)) n
    --       ],

    --   bgroup "FS" [
    --       bench "Count" $ nf (\n -> FS.runState (times n $ FS.modify @Int (+1)) 0) n
    --       ],

    --   bgroup "MTL" [
    --       bench "Count" $ nf (\n -> runState (times n $ modify @Int (+1)) 0) n
    --       ]
    --   ],

    -- bgroup "test2" [


    --   bench "MTL" $
    --     whnf ((`runReader` False) . (`runStateT` True) .
    --           (`runReaderT` 0) . (`runStateT` 0) . test2mtl) n,

    -- -- Only ~ 15% gains on fused handler!!!
    --   bgroup "Freer" [
    --     bench "Normal handlers" $
    --       whnf (F.run . (`F.runReader` False) . (`F.runState` True) .
    --             (`F.runReader` 0) . (`F.runState` 0) . test2F) n,
    --     bench "Fused handler" $
    --       whnf (bigHandler 0 0 True False . test2F) n
    --     ]
    --   ]


    ]

