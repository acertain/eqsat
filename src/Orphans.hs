{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Orphans (arrayBundle, MonadPrim) where

import Prelude hiding (fail)
import Control.Monad.Primitive
import Data.Monoid
import Control.Monad.Fail
import Control.Monad.IO.Class (MonadIO(liftIO))
import Data.Primitive.Array (indexArrayM, Array, sizeofArray)
import Data.Vector.Fusion.Bundle.Monadic hiding (toList,fromList)
import Data.Vector.Fusion.Stream.Monadic hiding (toList,fromList)
import Data.Vector.Fusion.Util (Box(..))
import Data.Vector.Fusion.Bundle.Size (Size(Exact))

instance PrimMonad m => PrimMonad (Alt m) where
  type PrimState (Alt m) = PrimState m
  primitive a = Alt (primitive a)
  {-# INLINE primitive #-}
instance MonadFail m => MonadFail (Alt m) where
  fail a = Alt (fail a)
  {-# INLINE fail #-}
instance MonadIO m => MonadIO (Alt m) where
  liftIO a = Alt (liftIO a)
  {-# INLINE liftIO #-}


class (PrimMonad m, s ~ PrimState m) => MonadPrim s m | m -> s
instance (PrimMonad m, s ~ PrimState m) => MonadPrim s m

arrayBundle :: Monad m => Array a -> Bundle m v a
{-# INLINE [1] arrayBundle #-}
arrayBundle a = a `seq` n `seq` fromStream (Stream step 0) (Exact n)
  where
    n = sizeofArray a

    {-# INLINE step #-}
    step i | i >= n = return Done
           | otherwise = case indexArrayM a i of
                           Box x -> return $ Yield x (i+1)
