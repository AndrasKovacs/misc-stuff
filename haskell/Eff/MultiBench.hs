{-# language FlexibleContexts, BangPatterns, TypeApplications, GADTs, TypeFamilies,
    NoMonoLocalBinds, GeneralizedNewtypeDeriving, DeriveFunctor,
    DataKinds, NoMonomorphismRestriction #-}

import Control.Monad
import Data.Monoid
import Criterion.Main
import System.Random

import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Writer.Strict
import Control.Monad.Except
import Control.Monad.Identity

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

{- bench TODO
  - multihandler for Freer
-}

{-  notes :
  - Oleg freer bench almost certainly without any optimization (LOL)
  - existing benchmarks are pretty shit
-}


test1 :: MonadState Int m => Int -> m Int
test1 n = foldM f 1 [0..n] where
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

-- monomorphic stack that uses all effects
test2 :: Int -> StateT Int (ReaderT Int (StateT Bool (Reader Bool))) ()
test2 n = replicateM_ n $ do
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


-- -- monomorphic stack that uses all effects
-- test2 :: Int -> (ReaderT Int (StateT Bool (Reader Bool))) ()
-- test2 n = replicateM_ n $ do
--   rint  <- ask
--   rbool <- lift $ lift $ ask
--   lift $ modify' $ \b -> if b then b && rbool else rint < 20

-- test2F :: Int -> F.Eff [F.Reader Int, F.State Bool, F.Reader Bool] ()
-- test2F n = replicateM_ n $ do
--   rint <- F.ask @Int
--   rbool <- F.ask @Bool
--   F.modify @Bool $ \b -> if b then b && rbool else rint < 20


main = do
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

    -- literally no overhead, no slowdown for large stack
    -- bgroup "MTL" [
    --   bench "SR"    $ whnf (runS . runRT . test1) n,
    --   bench "SRR"   $ whnf (runS . runRT . runRT . test1) n,
    --   bench "SRRR"  $ whnf (runS . runRT . runRT . runRT . test1) n,
    --   bench "SRRRR" $ whnf (runS . runRT . runRT . runRT . runRT . test1) n,
    --   bench "RS"    $ whnf (runR . runST . test1) n,
    --   bench "RRS"   $ whnf (runR . runRT . runST . test1) n,
    --   bench "RRRS"  $ whnf (runR . runRT . runRT . runST . test1) n,
    --   bench "RRRRS" $ whnf (runR . runRT . runRT . runRT . runST . test1) n,
    --   bench "S"     $ whnf (runS . test1) n
    --   ],


    -- Freer slower than mtl by about 10x, but doesn't slow much for large stack
    bgroup "Freer" [
      bench "SR"    $ whnf (F.run . runSF . runRF . test1F) n,
      bench "SRR"   $ whnf (F.run . runSF . runRF . runRF . test1F) n,
      bench "SRRR"  $ whnf (F.run . runSF . runRF . runRF . runRF . test1F) n,
      bench "SRRRR" $ whnf (F.run . runSF . runRF . runRF . runRF . runRF . test1F) n,
      bench "RS"    $ whnf (F.run . runRF . runSF . test1F) n,
      bench "RRS"   $ whnf (F.run . runRF . runRF . runSF . test1F) n,
      bench "RRRS"  $ whnf (F.run . runRF . runRF . runRF . runSF . test1F) n,
      bench "RRRRS" $ whnf (F.run . runRF . runRF . runRF . runRF . runSF . test1F) n,
      bench "S"     $ whnf (F.run . runSF . test1F) n
      ],

    bgroup "EffInference" [
      bench "SR"    $ whnf (I.run . runSI . runRI . test1I) n,
      bench "SRR"   $ whnf (I.run . runSI . runRI . runRI . test1I) n,
      bench "SRRR"  $ whnf (I.run . runSI . runRI . runRI . runRI . test1I) n,
      bench "SRRRR" $ whnf (I.run . runSI . runRI . runRI . runRI . runRI . test1I) n,
      bench "RS"    $ whnf (I.run . runRI . runSI . test1I) n,
      bench "RRS"   $ whnf (I.run . runRI . runRI . runSI . test1I) n,
      bench "RRRS"  $ whnf (I.run . runRI . runRI . runRI . runSI . test1I) n,
      bench "RRRRS" $ whnf (I.run . runRI . runRI . runRI . runRI . runSI . test1I) n,
      bench "S"     $ whnf (I.run . runSI . test1I) n
      ]

    -- bgroup "MTL" [
    --   bench "SANDWICH" $
    --     whnf ((`runReader` False) . (`runStateT` True) .
    --           (`runReaderT` 0) . (`runStateT` 0) . test2) n
    --   ]

    -- -- Only ~ 15% gains on bighandler!!!
    -- bgroup "Freer" [
    --   bench "SANDWICH" $
    --     whnf (F.run . (`F.runReader` False) . (`F.runState` True) .
    --           (`F.runReader` 0) . (`F.runState` 0) . test2F) n,
    --   bench "Bighandler" $
    --     whnf (bigHandler 0 0 True False . test2F) n
    -- ]

    -- bgroup "MTL" [
    --   bench "SANDWICH" $
    --     whnf ((`runReader` False) . (`runStateT` True) .
    --           (`runReaderT` 0) . test2) n
    --   ],

    -- -- Freer slower than mtl by about 10x, but doesn't slow much for large stack
    -- bgroup "Freer" [
    --   bench "SANDWICH" $
    --     whnf (F.run . (`F.runReader` False) . (`F.runState` True) .
    --           (`F.runReader` 0)  . test2F) n
    -- ]




    -- Writer is shit as we've all known, also slower when stacked
    -- state = fast writer with very little stack overhead


    -- You don't pay for what you don't use -- 220 ms for all sizes
    -- bgroup "Freer" [
    --   bench "SW"     $ whnf (F.run . runSF . runWF . test1F) n,
    --   bench "SWW"    $ whnf (F.run . runSF . runWF . runWF . test1F) n,
    --   bench "SWWW"   $ whnf (F.run . runSF . runWF . runWF . runWF . test1F) n,
    --   bench "SWWWW"  $ whnf (F.run . runSF . runWF . runWF . runWF . runWF . test1F) n,
    --   bench "WS"     $ whnf (F.run . runWF . runSF . test1F) n,
    --   bench "WWS"    $ whnf (F.run . runWF . runWF . runSF . test1F) n,
    --   bench "WWWS"   $ whnf (F.run . runWF . runWF . runWF . runSF . test1F) n,
    --   bench "WWWWS"  $ whnf (F.run . runWF . runWF . runWF . runWF . runSF . test1F) n,
    --   bench "S"      $ whnf (F.run . runSF . test1F) n
    --   ],

    -- bgroup "Freer" [
    --   bench "SR"    $ whnf (F.run . runSF . runRF . test1F) n,
    --   bench "SRR"   $ whnf (F.run . runSF . runRF . runRF . test1F) n,
    --   bench "SRRR"  $ whnf (F.run . runSF . runRF . runRF . runRF . test1F) n,
    --   bench "SRRRR" $ whnf (F.run . runSF . runRF . runRF . runRF . runRF . test1F) n,
    --   bench "RS"    $ whnf (F.run . runRF . runSF . test1F) n,
    --   bench "RRS"   $ whnf (F.run . runRF . runRF . runSF . test1F) n,
    --   bench "RRRS"  $ whnf (F.run . runRF . runRF . runRF . runSF . test1F) n,
    --   bench "RRRRS" $ whnf (F.run . runRF . runRF . runRF . runRF . runSF . test1F) n,
    --   bench "S"     $ whnf (F.run . runSF . test1F) n
    --   ],

    -- bgroup "Eff" [
    --   bench "SW"     $ whnf (E.run . runSE . runWE . test1E) n,
    --   bench "SWW"    $ whnf (E.run . runSE . runWE . runWE . test1E) n,
    --   bench "SWWW"   $ whnf (E.run . runSE . runWE . runWE . runWE . test1E) n,
    --   bench "SWWWW"  $ whnf (E.run . runSE . runWE . runWE . runWE . runWE . test1E) n,
    --   bench "WS"     $ whnf (E.run . runWE . runSE . test1E) n,
    --   bench "WWS"    $ whnf (E.run . runWE . runWE . runSE . test1E) n,
    --   bench "WWWS"   $ whnf (E.run . runWE . runWE . runWE . runSE . test1E) n,
    --   bench "WWWWS"  $ whnf (E.run . runWE . runWE . runWE . runWE . runSE . test1E) n,
    --   bench "S"      $ whnf (E.run . runSE . test1E) n
    --   ],

    -- bgroup "Eff" [
    --   bench "SR"    $ whnf (E.run . runSE . runRE . test1E) n,
    --   bench "SRR"   $ whnf (E.run . runSE . runRE . runRE . test1E) n,
    --   bench "SRRR"  $ whnf (E.run . runSE . runRE . runRE . runRE . test1E) n,
    --   bench "SRRRR" $ whnf (E.run . runSE . runRE . runRE . runRE . runRE . test1E) n,
    --   bench "RS"    $ whnf (E.run . runRE . runSE . test1E) n,
    --   bench "RRS"   $ whnf (E.run . runRE . runRE . runSE . test1E) n,
    --   bench "RRRS"  $ whnf (E.run . runRE . runRE . runRE . runSE . test1E) n,
    --   bench "RRRRS" $ whnf (E.run . runRE . runRE . runRE . runRE . runSE . test1E) n,
    --   bench "S"     $ whnf (E.run . runSE . test1E) n
    --   ]


    ]
