{-# language BlockArguments #-}
{-# language TupleSections #-}
{-# language PatternSynonyms #-}
module BoxedVec where

import Control.Monad.Primitive
import Control.Monad.ST
import Data.Bits
import Data.Primitive.Array
import Data.Primitive.MutVar
import Data.Foldable


-- transient, slice from 0 to ix
data Vec s a = Vec {-# unpack #-} !Int {-# unpack #-} !(MutableArray s a)

-- non-backtracking writes by default

-- newtype Vec s a = Vec (MVar s (Slab s a))

pattern DEFAULT_SIZE :: Int
pattern DEFAULT_SIZE = 4

newVec_ :: (PrimMonad m) => m (Vec (PrimState m) a)
newVec_ = newVec 0

newVec :: (PrimMonad m) => Int -> m (Vec (PrimState m) a)
newVec n = stToPrim do Vec 0 <$> newArray n undefined
{-# inline newVec #-}

resizeMutableArray :: PrimMonad m => MutableArray (PrimState m) a -> Int -> m (MutableArray (PrimState m) a)
resizeMutableArray a n' = do
  let n = sizeofMutableArray a
  a' <- newArray n' undefined
  copyMutableArray a' 0 a 0 (min n n')
  pure a'

-- ensure space for k total elements
reserveMutableArray :: PrimMonad m => MutableArray (PrimState m) a -> Int -> m (MutableArray (PrimState m) a)
reserveMutableArray a k = do
  let n = sizeofMutableArray a
  if k <= n then pure a else resizeMutableArray a (k*2)
{-# inline reserveMutableArray #-}

addVec :: (PrimMonad m) => a -> Vec (PrimState m) a -> m (Int, Vec (PrimState m) a)
addVec a (Vec i pa) = stToPrim do
  pa' <- reserveMutableArray pa (i+1)
  writeArray pa' i a
  return (i, Vec (i+1) pa')
{-# inline addVec #-}

subVec :: (PrimMonad m) => Vec (PrimState m) a -> m (Vec (PrimState m) a)
subVec (Vec i pa) = stToPrim do
  let n = sizeofMutableArray pa
  let n' = unsafeShiftR n 2
  if i >= n' then return $ Vec (i-1) pa
  else Vec (i-1) <$> resizeMutableArray pa (n*2)

readVec :: (PrimMonad m) => Vec (PrimState m) a -> Int -> m a
readVec (Vec _ pa) i = readArray pa i
{-# inline readVec #-}

-- doesn't change shape
writeVec :: (PrimMonad m) => Vec (PrimState m) a -> Int -> a -> m ()
writeVec (Vec _ pa) i a = writeArray pa i a
{-# inline writeVec #-}

sizeVec :: Vec s a -> Int
sizeVec (Vec i _ ) = i
{-# inline sizeVec #-}

-- append b to a
appendVec :: PrimMonad m => Vec (PrimState m) a -> Vec (PrimState m) a -> m (Vec (PrimState m) a)
appendVec (Vec ai aa) (Vec bi ba) = do
  aa' <- reserveMutableArray aa (ai+bi)
  copyMutableArray aa' ai ba 0 bi
  pure $ Vec (ai+bi) aa'

-- this would play the role of std::vector, non-transient non-thread-safe version
newtype Vector s a = Vector (MutVar s (Vec s a))

instance Eq (Vector s a) where
  Vector a == Vector b = a == b

newVector_ :: (PrimMonad m) => m (Vector (PrimState m) a)
newVector_ = newVector 0
{-# inline newVector_ #-}

newVector :: (PrimMonad m) => Int -> m (Vector (PrimState m) a)
newVector n = stToPrim do
  v <- newVec n
  Vector <$> newMutVar v
{-# inline newVector #-}

-- not thread safe
nonAtomicModifyVector :: PrimMonad m => Vector (PrimState m) a -> (Vec (PrimState m) a -> ST (PrimState m) (r, Vec (PrimState m) a)) -> m r
nonAtomicModifyVector (Vector ref) k = stToPrim do
  v <- readMutVar ref
  (r, v') <- k v
  r <$ writeMutVar ref v'
{-# inline nonAtomicModifyVector #-}

modifyVector :: PrimMonad m => Vector (PrimState m) a -> (Vec (PrimState m) a -> ST (PrimState m) (Vec (PrimState m) a)) -> m ()
modifyVector (Vector ref) k = stToPrim $ (readMutVar ref >>= k) >>= writeMutVar ref
{-# inline modifyVector #-}
  
addVector :: (PrimMonad m) => a -> Vector (PrimState m) a -> m Int
addVector a v = nonAtomicModifyVector v \vec -> addVec a vec
{-# inline addVector #-}

subVector :: (PrimMonad m) => Vector (PrimState m) a -> m ()
subVector v = modifyVector v subVec
{-# inline subVector #-}

readVector :: (PrimMonad m) => Vector (PrimState m) a -> Int -> m a
readVector (Vector ref) i = readMutVar ref >>= \(Vec _ pa) -> readArray pa i
{-# inline readVector #-}

writeVector :: (PrimMonad m) => Vector (PrimState m) a -> Int -> a -> m ()
writeVector (Vector ref) i a = readMutVar ref >>= \vec -> writeVec vec i a
{-# inline writeVector #-}

sizeVector :: PrimMonad m => Vector (PrimState m) a -> m Int
sizeVector (Vector ref) = stToPrim $ sizeVec <$> readMutVar ref
{-# inline sizeVector #-}

-- TODO: maybe freeze into vector:Vector to take advantage of fusion?
freezeVector :: PrimMonad m => Vector (PrimState m) a -> m (Array a)
freezeVector (Vector ref) = readMutVar ref >>= \(Vec i pa) -> freezeArray pa 0 i
{-# inline freezeVector #-}

-- append b to a
appendVector :: PrimMonad m => Vector (PrimState m) a -> Vector (PrimState m) a -> m ()
appendVector (Vector ar) (Vector br) = do
  a <- readMutVar ar
  b <- readMutVar br
  writeMutVar ar =<< appendVec a b
