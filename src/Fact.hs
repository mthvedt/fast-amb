{-# LANGUAGE
  DeriveGeneric,
  ExistentialQuantification,
  TemplateHaskell
#-}

module Fact where

import GHC.Generics (Generic)

import Control.Monad
import Data.Hashable
import qualified Data.Map as Tree
import qualified Data.HashMap.Lazy as Map
import qualified Data.HashSet as Set
import qualified Data.Vector as Vec
import Data.Maybe

import Control.Lens
import Control.Lens.TH

import Amb

type Vector = Vec.Vector
type Map = Map.HashMap
type Set = Set.HashSet
type Tree = Tree.Map

instance Hashable a => Hashable (Vec.Vector a) where
  hashWithSalt salt = hashWithSalt salt . Vec.toList

data FactElt = IntElt Int | StringElt String deriving (Eq, Generic, Ord)

instance Hashable FactElt

newtype Tuple = Tuple (Vector FactElt) deriving (Eq, Generic, Ord)

instance Hashable Tuple

class FactNode n where

data PolyFactNode = forall n. PolyFactNode n

instance FactNode PolyFactNode where

polyFactNode :: FactNode n => n -> PolyFactNode
polyFactNode = PolyFactNode

class FactSet s where
  freshEntity :: s -> (Int, s)
  addNode :: FactNode n => Int -> n -> s -> s
  getNode :: Int -> s -> Maybe PolyFactNode

-- TODO: better tracking of entities
data SimpleFactSet = SimpleFactSet {
  _entities :: Tree Int Int,
  _simpleFactSetNodes :: Map Int PolyFactNode
}

makeLenses ''SimpleFactSet

simpleFactSet :: SimpleFactSet
simpleFactSet = SimpleFactSet Tree.empty Map.empty

instance FactSet SimpleFactSet where
  freshEntity s = (i, over entities (Tree.insert (i + 1) 1) s) where
    i = maybe (negate 1) snd $ Tree.lookupLE maxBound $ view entities s
  addNode name n = over simpleFactSetNodes (Map.insert name (polyFactNode n))
  getNode name s =  Map.lookup name $ view simpleFactSetNodes s

class FactNode b => TupleBase b where
  put :: Tuple -> b -> b
  del :: Tuple -> b -> b

newtype SimpleBase = SimpleBase {
  _simpleBaseValues :: Set Tuple
}

makeLenses ''SimpleBase

instance FactNode SimpleBase where

instance TupleBase SimpleBase where
  put tuple = over simpleBaseValues (Set.insert tuple)
  del tuple = over simpleBaseValues (Set.delete tuple)

newtype TupleIndex = TupleIndex {
  _index :: Tree Tuple Tuple
}

-- class FactBase b where
--   put :: Foldable f => b -> f FactElt -> b
  -- query :: Amb a => b -> [FactElt] -> a [FactElt]

-- data SimpleBase = SimpleBase {
--   _baseIsValue :: Bool,
--   _childBases :: Maybe (Map.HashMap FactElt SimpleBase)
-- }
--
-- Lens.makeLenses ''SimpleBase
--
-- simpleBase :: SimpleBase
-- simpleBase = SimpleBase False Nothing
--
-- iterateBase :: Amb a => [FactElt] -> SimpleBase -> a [FactElt]
-- iterateBase prefix (SimpleBase b children) = join $ amb [first, rest] where
--   first = if b then amb [prefix] else amb []
--   rest = join . amb $ Map.foldrWithKey (\k v r -> iterateBase (prefix ++ [k]) v:r) [] (fromMaybe Map.empty children)
--
-- queryHelper :: Amb a => [FactElt] -> SimpleBase -> [FactElt] -> a [FactElt]
-- queryHelper prefix b [] = iterateBase prefix b
-- queryHelper prefix (SimpleBase _ (Just m)) (fact:facts) = case Map.lookup fact m of
--   Just b -> queryHelper (prefix ++ [fact]) b facts
--   Nothing -> amb []
-- queryHelper _ (SimpleBase _ Nothing) _ = amb []
--
-- instance FactBase SimpleBase where
--   put b [] = Lens.set baseIsValue True b
--   put (SimpleBase v mm) (fact:facts) = SimpleBase v . Just $ Map.alter updatef fact (fromMaybe Map.empty mm) where
--     updatef entry = Just $ put (fromMaybe simpleBase entry) facts
--   query = queryHelper []
