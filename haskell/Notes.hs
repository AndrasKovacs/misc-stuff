{-# language GADTs, StandaloneDeriving, NoTypeInType #-}

module Notes where

data False

data R = MkR {proj :: R -> False}

f :: R -> False
f = \x -> proj x x
{-# noinline f #-}

omega :: False
omega = f (MkR f)

main = do
  print (omega `seq` ())

