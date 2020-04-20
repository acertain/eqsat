{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ImplicitParams, ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances #-}
{-# LANGUAGE TypeFamilies, RankNTypes #-}
{-# LANGUAGE DeriveTraversable, DeriveFunctor, DeriveAnyClass, DeriveGeneric #-}
{-# LANGUAGE TemplateHaskell #-}


-- | e-peg/egraph
--
-- TODO:
-- - merging terms / adding to equiv classes
--   - congr closure
-- - equality constraints / nonlinear variables
-- - aggregates
-- - tests
-- - Congruence Closure in Intensional Type Theory
--     is just use het eq + a proof reconstruction step?
--
-- - think about doing something special for e.g. AC

-- TODO: would be nice to be able to use union-find like when no function symbols
-- & only do work for function symbols
module Epeg where

import GHC.Weak
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

import Data.Monoid (Alt(..))


class (PrimMonad m, s ~ PrimState m) => MonadPrim s m | m -> s
instance (PrimMonad m, s ~ PrimState m) => MonadPrim s m


data TmAlg f =
    Add f f
  | Mul f f
  | Var Int
  deriving (Eq,Show,Functor,Foldable,Traversable,Hashable,Generic)


matchAlg :: TmAlg a -> TmAlg b -> Maybe [(a,b)]
matchAlg x y | (() <$ x) == (() <$ y) = Just $ zip (toList x) (toList y)
             | otherwise = Nothing

data Pattern = Pat (TmAlg Pattern) | PatVar
  deriving (Eq, Hashable, Generic)




newtype WkTermSet s = WkTermSet (Vector s (Weak (Term s)))

data Term s = Term {
  -- union-find elem
  tmClass :: {-# UNPACK #-} !(EquivClass s),
  -- currently store an EquivClass here, but instead could make Term be a struct/ArrayArray, have EquivClass be a field, store `ClassRoot`s in body, & mutate them on merge
  -- or store ClassRoot immutably & not expose Term (only store it in equiv classes)
  tmBody :: TmAlg (EquivClass s)
}



instance Show (Term s) where
  showsPrec i (Term b _) = showsPrec i b



-- union find

newtype EquivClass s = ClassRef (MutVar s (ClassContents s))
  deriving (Eq)

-- immutable field = only updated on merge
data ClassRoot s = ClassRoot {
    -- ========= union find
    -- | TODO: this is just len members?
    --
    -- probably. in theory, could have stuff in union-find not in members
    -- to like orient equations
    -- also would need to adjust this for Find (= removed from union find)
    clsSize :: {-# UNPACK #-} !Int,
    -- ========= congruence closure
    -- TODO: make this indexed, or mb only index when we're the first arg?
    clsParents :: {-# UNPACK #-} !(Vector s (Weak (Term s))),
    -- ========= indexes
    -- | List of terms in us that we want to keep around
    --
    -- if `a == b` and the terms `f a` and `f b` exist, we only store one here
    -- and set the other's equiv class to Find
    --
    -- ideally this should be a lazy container, to make merges cost union-find + parents when possible
    --
    -- TODO: consider sorting or indexing this, or replacing it with a HashMap or an immutable vector
    clsMembers :: {-# UNPACK #-} !(Vector s (Term s)),
    -- | A function of members, updated incrementally
    clsPatterns :: {-# UNPACK #-} !(MutVar s (HashMap Pattern (PatternState s)))
  }

instance Eq (ClassRoot s) where
  x == y = clsMembers x == clsMembers y

data ClassContents s =
    -- TODO: describe proof annotation + recon thingy
    -- basic idea is when merge classes w/ root `a` and `b`, just ann new edge w/ equality `x = y` that caused merge (that might be between children of a & b), and figure out the proofs of `a = x` and `y = b` at proof reconstruction time
   -- TODO: figure out its asymtotics & if it's good & stuff
   -- TODO: could point to Term instead of its EquivClass here?
    Child (EquivClass s)
    -- | Run findTerm on the term this belongs to to determine its equivalence class
  | Find
  -- -- probably could get away without the ref to the term
  -- TODO: add parents vec to One?
  -- | Equivalence class with one member
  | One !(Term s)
  -- | Equivalence class with zero members
  | Zero
  | Root (ClassRoot s)


classRoot :: MonadPrim s m => EquivClass s -> m (ClassRoot s)
classRoot (ClassRef c) = readMutVar c >>= \x -> case x of
  Child h -> classRoot h
  Find -> undefined -- TODO
  Root r -> pure r

instance Show (EquivClass s) where
  showsPrec i v = unsafePerformIO $ unsafeSTToIO $ do
    r <- classRoot v
    x <- readVector (clsMembers r) 0
    pure $ showsPrec i x



-- | Pattern + Term = Quer
--
-- Materialized query state
--
-- Used to store parent queries to re-run once a child query matches
--
-- TODO: add QueryTopLevel? since queries ~= callbacks
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




data Aggregate where
  Agg :: (Monoid a, Typeable a) => Proxy a -> Aggregate



makeLenses ''PatternState

data EqSatState s = EqSatState {
  -- set of all terms without children, used for hash-consing
  leaves :: WkTermSet s
}

-- need s ~ RealWorld to use Weak i think?
type EqSat s = (?eqsat :: EqSatState s, s ~ RealWorld)


runQuery :: EqSat s => Query s -> IO ()
-- TODO: assert or check not already matched?
runQuery q@(Query p@(Pat pa) tm) = case matchAlg pa (tmBody tm) of
  Nothing -> pure ()
  Just bnds -> do
    x <- runMaybeT $ for bnds \(pat,cls) -> when (pat /= PatVar) $ do
      cr <- classRoot cls
      ps <- liftIO $ patternState cr pat
      if has (psMatches . _head) ps then
        pure ()
      else do
        modifyMutVar (clsPatterns cr) (\m -> m & ix p . psBlockedQueries %~ (q:))
        mzero
    when (has _Just x) $ do
      r <- mkWeak tm tm Nothing
      cr <- classRoot (tmClass tm)
      m <- readMutVar (clsPatterns cr)
      if has (ix p . psBlockedQueries . _head) m then do
        writeMutVar (clsPatterns cr) (m & ix p .~ PatternMatches [] [r])
        forOf_ (ix p . psBlockedQueries . each) m runQuery
      else do
        writeMutVar (clsPatterns cr) (m & ix p . psMatches %~ (r:))
  where
  patternState :: EqSat s => ClassRoot s -> Pattern -> IO (PatternState s)
  patternState cls p = do
    m <- readMutVar $ clsPatterns cls
    case m ^? ix p of
      Just r -> pure r
      Nothing -> do
        writeMutVar (clsPatterns cls) (m & at p .~ Just (PatternNoMatches []))
        members <- freezeVector $ clsMembers cls
        for_ members \x -> runQuery $ Query p x
        m' <- readMutVar (clsPatterns cls)
        pure $ m' ^?! ix p

newEmptyCls :: IO (EquivClass RealWorld)
newEmptyCls = ClassRef <$> newMutVar Zero

findTerm :: EqSat s => TmAlg (Term s) -> IO (Maybe (Term s))
findTerm tm = do
  tm' <- traverse (classRoot . tmClass) tm
  case toList tm' of
    chld:_ -> do
      let vec = clsParents chld
      sz <- sizeVector vec
      runMaybeT $ getAlt $ foldMap (f tm' vec) [0..(sz-1)]
    _ -> do
      -- TODO: check leaves
      pure Nothing
  where
    f tm1 vec i = do
      tmref <- readVector (coerce vec) i
      Just tm2 <- liftIO $ deRefWeak tmref
      tm2' <- traverse classRoot $ tmBody tm2
      if tm1 == tm2' then pure tm2
      else mempty

makeTerm :: EqSat s => TmAlg (Term s) -> IO (Term s)
makeTerm tm = findTerm tm >>= \w -> case w of
  Just x -> pure x
  Nothing -> do
    var <- newMutVar Zero
    let bd = fmap tmClass tm
    let tm' = Term (ClassRef var) bd
    writeMutVar var $ One tm'
    tmref <- mkWeak tm' tm' Nothing
    for_ (toList bd) \cls -> (addVector tmref . clsParents) =<< classRoot cls
    when (null $ toList bd) $ void $ addVector tmref (coerce $ leaves ?eqsat)
    pure tm'


-- -- merge a and b. both a and b are invalid after, use the returned class
-- merge :: Cls -> Cls -> IO Cls
-- -- TODO: merge into smaller
-- merge a b = do
--   a_ms <- freezeVector (clsMembers a)
--   b_ms <- freezeVector (clsMembers b)
--   b_ps <- freezeVector (clsParents b)

--   for b_ms $ \bm -> do
--     for (tmChildren bm) \cls -> do
--       -- update cls's b parent to point to a
--       undefined
--     when (elem bm a_ms) $ error "term in multiple equiv classes"
--     addVector bm (clsMembers a)
--     undefined
--   -- appendVector (clsMembers a) (clsMembers b)
--   -- appendVector (clsParents a) (clsParents b)
  
--   -- check for parent merges
--   -- check for fundeps causing member merges
--   -- update patterns
--   undefined
  


withEqSat :: (EqSat RealWorld => IO r) -> IO r
withEqSat f = do
  st <- EqSatState <$> (WkTermSet <$> newVector_)
  let ?eqsat = st
  f

testTm :: IO (Term RealWorld)
testTm = build $ Add (Var 1) (Add (Var 2) (Var 3))


class BuildTerm a where
  buildTerm :: EqSat s => TmAlg a -> IO (Term s)

instance BuildTerm (Term RealWorld) where
  buildTerm = makeTerm
instance BuildTerm a => BuildTerm (TmAlg a) where
  buildTerm a = buildTerm =<< traverse buildTerm a


-- using IncoherentInstances to make build infer
class BuildTerm a => Buildable a
instance Buildable x => Buildable (TmAlg x)
instance {-# INCOHERENT #-} a ~ Term RealWorld => Buildable a

build :: Buildable a => TmAlg a -> IO (Term RealWorld)
build x = withEqSat (buildTerm x)
