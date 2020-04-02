{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ImplicitParams, ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts, NoMonoLocalBinds, FlexibleInstances #-}
{-# LANGUAGE TypeFamilies, RankNTypes #-}
{-# LANGUAGE DeriveTraversable, DeriveFunctor, DeriveAnyClass, DeriveGeneric #-}
{-# LANGUAGE TemplateHaskell #-}

-- | e-peg
--
-- the traditional smt egraph stores terms with equal children multiple times,
-- and only keeps track of equality between them. we merge terms with equal children
--

-- TODO:
-- - merging terms / adding to equiv classes
--   - congr closure
-- - equality constraints / nonlinear variables
-- - aggregates
-- - tests

module Epeg where

import GHC.Weak
import Data.Monoid
import Control.Monad.Trans.Maybe
import Control.Monad.Primitive
import Control.Monad
import Data.Foldable
import GHC.Generics (Generic)
import Control.Lens

import Data.HashMap.Strict (HashMap)
import Data.Hashable
import Data.Primitive.MutVar

import Data.Coerce

import System.IO.Unsafe
import Control.Monad.ST.Unsafe

import Orphans ()

import BoxedVec
import Data.Proxy (Proxy)
import Data.Typeable (Typeable)
import Data.Traversable (for)
import Control.Monad.IO.Class (MonadIO(liftIO))

data TmAlg f =
    Add f f
  | Mul f f
  | Var Int
  deriving (Eq,Show,Functor,Foldable,Traversable,Hashable,Generic)

tmChildren :: TmAlg f -> [f]
tmChildren x = toList x

matchAlg :: TmAlg a -> TmAlg b -> Maybe [(a,b)]
matchAlg x y | (() <$ x) == (() <$ y) = Just $ zip (toList x) (toList y)
             | otherwise = Nothing

data Pattern = Pat (TmAlg Pattern) | PatVar
  deriving (Eq, Hashable, Generic)

newtype WkTermSet s = WkTermSet (Vector s (Weak (EquivClass s), Int))

-- data Term s = Term {
--   _tmClass :: MutVar s (EquivClass s),
--   _tmNext :: MutVar s (Term s),
--   _tmBody :: TmAlg (EquivClass s)
-- }

type Term s = TmAlg (EquivClass s)

-- TODO: should these be weak?
data EquivClassBackref s =
  -- terms that have us as their child: class + index into members
    EqClassRef (EquivClass s) Int
  -- we're in a weak term set, index
  | TermSetRef (WkTermSet s) Int


-- TODO: what if tm gets deleted?
-- pattern + term = query
-- TODO: add QueryTopLevel?
data Query s = Query {
  -- pattern we're trying to match
  queryPat :: Pattern,
  -- term to match against pattern
  queryTm :: Term s
}

-- need per class map (term => patterns matching that term)
-- or store in terms patterns matching that term?
-- to look at when deleting terms
data PatternState s = PatternMatches {
  _psMatchedQueries :: [(Pattern, Term s)],
  -- could instead do indexes into members
  _psMatches :: [Weak (Term s)]
} | PatternNoMatches {
  _psBlockedQueries :: [Query s]
}


-- TODO: need at least count for sampling
-- should just do group (mb monoid too?) aggregates


data Aggregate where
  Agg :: (Monoid a, Typeable a) => Proxy a -> Aggregate

data EquivClass s = EquivClass {
  clsMembers :: Vector s (Term s),
  -- todo: len parents is effectively a ref count, consider using it?
  clsParents :: Vector s (EquivClassBackref s),
  -- list of indexes into members
  -- should be Maybe (NonEmpty Int)?
  -- or just use [Int]?
  clsPatterns :: MutVar s (HashMap Pattern (PatternState s))
}

instance Eq (EquivClass s) where
  a == b = clsMembers a == clsMembers b


instance Show (EquivClass s) where
  showsPrec i c = unsafePerformIO $ unsafeSTToIO $ do
    x <- readVector (clsMembers c) 0
    pure $ showsPrec i x

makeLenses ''PatternState

data EqSatState s = EqSatState {
  -- set of all terms without children, used for hash-consing
  leaves :: WkTermSet s
}

-- a + b == b + a

type EqSat = (?eqsat :: EqSatState RealWorld)

type Cls = EquivClass RealWorld
type Tm = Term RealWorld


patternState :: EqSat => Cls -> Pattern -> IO (PatternState RealWorld)
patternState cls p = do
  m <- readMutVar $ clsPatterns cls
  case m ^? ix p of
    Just r -> pure r
    Nothing -> do
      writeMutVar (clsPatterns cls) (m & at p .~ Just (PatternNoMatches []))
      members <- readVectorList $ clsMembers cls
      for_ members \x -> runQuery $ Query p x
      m' <- readMutVar (clsPatterns cls)
      pure $ m' ^?! ix p

runQuery :: EqSat => Query RealWorld -> IO ()
-- TODO: assert or check not already matched?
-- i think want version that checks but normally dont?
runQuery q@(Query p@(Pat pa) tm) = case matchAlg pa tm of
  Nothing -> pure ()
  Just bnds -> do
    x <- runMaybeT $ for bnds \(pat,cls) -> when (pat /= PatVar) $ do
      ps <- liftIO $ patternState cls pat
      if has (psMatches . _head) ps then
        pure ()
      else do
        modifyMutVar (clsPatterns cls) (\m -> m & ix p . psBlockedQueries %~ (q:))
        mzero
    when (has _Just x) $ do
      r <- mkWeak tm tm Nothing
      Just cls <- findTm tm
      m <- readMutVar (clsPatterns cls)
      if has (ix p . psBlockedQueries . _head) m then do
        writeMutVar (clsPatterns cls) (m & ix p .~ PatternMatches [] [r])
        forOf_ (ix p . psBlockedQueries . each) m runQuery
      else do
        writeMutVar (clsPatterns cls) (m & ix p . psMatches %~ (r:))
 

newEmptyCls :: IO Cls
newEmptyCls = EquivClass <$> newVector 1 <*> newVector 1 <*> newMutVar mempty

newClass :: EqSat => Tm -> IO Cls
newClass tm = do
  cls <- newEmptyCls
  idx <- addVector tm (clsMembers cls)
  for_ (tmChildren tm) \cls' -> addVector (EqClassRef cls 0) (clsParents cls')
  when (null $ tmChildren tm) $ do
    wkcls <- mkWeak cls cls Nothing
    _ <- addVector (wkcls, idx) (coerce $ leaves ?eqsat)
    pure ()
  pure cls

findTm :: EqSat => Tm -> IO (Maybe Cls)
findTm tm = case tmChildren tm of
  chld:_ -> do
    -- Alt (MaybeT IO)
    let vec = clsParents chld
    sz <- sizeVector vec
    parent <- runMaybeT $ getAlt $ foldMap (f tm vec) [0..(sz-1)]
    pure parent
  _ -> do
    -- todo: check leaves
    pure Nothing

  where
    f tm1 vec i = do
      EqClassRef cls idx <- readVector (coerce vec) i
      tm2 <- readVector (clsMembers cls) idx
      if tm1 == tm2 then pure cls else mempty


mk :: EqSat => Tm -> IO Cls
mk tm = do
  x <- findTm tm
  case x of
    Nothing -> newClass tm
    Just cls -> pure cls


withEqSat :: (EqSat => IO r) -> IO r
withEqSat f = do
  st <- EqSatState <$> (WkTermSet <$> newVector_)
  let ?eqsat = st
  f

testTm :: IO Cls
testTm = build $ Add (Var 1) (Add (Var 2) (Var 3))


class BuildTerm a where
  buildTerm :: EqSat => TmAlg a -> IO Cls

instance BuildTerm (EquivClass RealWorld) where
  buildTerm = mk
instance BuildTerm a => BuildTerm (TmAlg a) where
  buildTerm a = buildTerm =<< traverse buildTerm a


-- using IncoherentInstances to make build infer
class BuildTerm a => Buildable a
instance Buildable x => Buildable (TmAlg x)
instance {-# INCOHERENT #-} a ~ EquivClass RealWorld => Buildable a

build :: Buildable a => TmAlg a -> IO Cls
build x = withEqSat (buildTerm x)
