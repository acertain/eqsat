{-# LANGUAGE TypeFamilies #-}
module Orphans where

import Prelude hiding (fail)
import Control.Monad.Primitive
import Data.Monoid
import Control.Monad.Fail
import Control.Monad.IO.Class (MonadIO(liftIO))

instance PrimMonad m => PrimMonad (Alt m) where
  type PrimState (Alt m) = PrimState m
  primitive a = Alt (primitive a)

instance MonadFail m => MonadFail (Alt m) where
  fail a = Alt (fail a)

instance MonadIO m => MonadIO (Alt m) where
  liftIO a = Alt (liftIO a)
