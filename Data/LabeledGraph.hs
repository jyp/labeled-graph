{-# LANGUAGE ScopedTypeVariables, ParallelListComp, RankNTypes, TypeOperators #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.LabeledGraph
-- Copyright   :  (c) The University of Glasgow 2002,
--                    Jean-Philippe Bernardy 2012-2016
-- License     :  BSD-style
--
-- Maintainer  :  JP Bernardy
-- Stability   :  experimental
-- Portability :  GHC
--
-- A version of the graph algorithms described in:
--
--   /Structuring Depth-First Search Algorithms in Haskell/,
--   by David King and John Launchbury.
--
-- And
--
--   /Cycle therapy: a prescription for fold and unfold on regular trees/
--   by Franklyn Turbak and J.B. Wells
--
--   Adaptation by JP Bernardy.
--
-----------------------------------------------------------------------------

module Data.LabeledGraph(

        -- * External interface

        -- At present the only one with a "nice" external interface
        -- stronglyConnComp, stronglyConnCompR, SCC(..), flattenSCC, flattenSCCs,

        -- * Graphs
        Graph, Table, Bounds, Edge, Vertex,

        -- ** Building graphs
        graphFromEdges, graphFromEdges', buildEdges, buildG, transposeG,
        -- reverseE,

        -- ** Graph properties

        vertices, edges,
        outdegree, indegree,
        unlabel,

        -- * Algorithms

        dfs, dff,
        topSort,
        components,
        scc, bcc,
        reachable, path,

        -- * Folding
        fold', scan', scan,

        -- * Unfolding
        unfold, unfoldMany,

        module Data.LabeledTree

    )  where

import Control.Monad (ap)
import Control.Monad.ST
import Data.Array.ST (STArray, newArray, readArray, writeArray)
import Data.LabeledTree (Tree(Node), Forest, (::>)((::>)) )
import qualified Data.Graph as Unlabeled
import Data.Graph as Data.LabeledGraph (Vertex,Table,Bounds)
import Data.STRef

-- import Control.DeepSeq (NFData(rnf))
import Data.Maybe
import Data.Array
import Data.List
import qualified Data.Map as M
import qualified Data.Set as S


unlabel :: Graph e -> Unlabeled.Graph
unlabel = fmap (fmap snd)

------------------------------------------------------------------------
--                                                                      -
--      Graphs
--                                                                      -
-------------------------------------------------------------------------

-- | Adjacency list representation of a graph, mapping each vertex to its
-- list of successors.
type Graph e  = Table [(e,Vertex)]
-- | An edge from the first vertex to the second.
type Edge e  = (Vertex,e,Vertex)


-- | Graph structure + colour on the vertices
data ColouredGraph c e = ColouredGraph (Graph e) (Colouring c)
type Colouring a = Vertex -> a


showWithColor :: forall a a1 i.
                   (Show a, Show a1, Show i, Ix i) =>
                   Array i a1 -> (i -> a) -> [Char]
showWithColor gr color = concat $ map showNode $ range $ bounds gr
  where
    showNode n = show n ++ ": " ++ show (color n) ++ " -> " ++ show (gr!n) ++ "\n"

-- debug
showDotFile :: forall a. Show a => Graph a -> [Char]
showDotFile gr =
    "digraph name {\n" ++
    "rankdir=LR;\n" ++
    (concatMap showEdge $ edges gr) ++
    "}\n"
    where showEdge (from, t, to) = show from ++ " -> " ++ show to ++
                                   " [label = \"" ++ show t ++ "\"];\n"


instance (Show c, Show e) => Show (ColouredGraph c e) where
    show (ColouredGraph gr col) = showWithColor gr col


-- | All vertices of a graph.
vertices :: Graph l -> [Vertex]
vertices  = indices

-- | All edges of a graph.
edges    :: Graph e -> [Edge e]
edges g   = [ (v,l,w) | v <- vertices g, (l,w) <- g!v ]


mapT    :: (Vertex -> a -> b) -> Table a -> Table b
mapT f t = array (bounds t) [ (,) v (f v (t!v)) | v <- indices t ]

-- | Build a graph from a list of edges.
buildG :: Bounds -> [Edge e] -> Graph e
buildG bounds0 edges0 = accumArray (flip (:)) [] bounds0 [(v, (l,w))
                                                         | (v,l,w) <- edges0]

-- | Turn nodes to vertices in a list of edges. To be composed with BuildG
buildEdges :: Ord nodeKey => [(nodeKey,edgeLabel,nodeKey)] ->
              (Bounds,[Edge edgeLabel],Vertex -> nodeKey)
buildEdges es = ((0,S.size keys - 1),map mkEdge es,flip S.elemAt keys)
  where keys = S.fromList [x | (s,_,t) <- es, x <- [s,t]]
        lkKey k = case S.lookupIndex k keys of
          Just ix -> ix
          Nothing -> error "LabeledGraph: unknown key"
        mkEdge (s,e,t) = (lkKey s,e,lkKey t)

-- | The graph obtained by reversing all edges.
transposeG  :: Graph e -> Graph e
transposeG g = buildG (bounds g) (reverseE g)

reverseE    :: Graph e -> [Edge e]
reverseE g   = [ (w, l, v) | (v, l, w) <- edges g ]

-- | A table of the count of edges from each node.
outdegree :: Graph e -> Table Int
outdegree  = mapT numEdges
             where numEdges _ ws = length ws

-- | A table of the count of edges into each node.
indegree :: Graph e -> Table Int
indegree  = outdegree . transposeG

-- | Identical to 'graphFromEdges', except that the return value
-- does not include the function which maps keys to vertices.  This
-- version of 'graphFromEdges' is for backwards compatibility.
graphFromEdges'
        :: Ord key
        => [(node, key, [(e,key)])]
        -> (Graph e, Vertex -> (node, key, [(e,key)]))
graphFromEdges' x = (a,b) where
    (a,b,_) = graphFromEdges x

-- | Build a graph from a list of nodes uniquely identified by keys,
-- with a list of keys of nodes this node should have edges to.
-- The out-list may contain keys that don't correspond to
-- nodes of the graph; they are ignored.
graphFromEdges
        :: forall key e node.
           Ord key
        => [(node, key, [(e,key)])]
        -> (Graph e, Vertex -> (node, key, [(e,key)]), key -> Maybe Vertex)
graphFromEdges edges0
  = (graph, \v -> vertex_map ! v, key_vertex)
  where
    max_v           = length edges0 - 1
    bounds0         = (0,max_v) :: (Vertex, Vertex)
    sorted_edges    = sortBy lt edges0
    edges1          = zipWith (,) [0..] sorted_edges

    graph :: Graph e
    graph           = array bounds0 [(,) v [(e,v') | (e,k) <- ks, let Just v' = key_vertex k]
                                    | (,) v (_,    _, ks) <- edges1]
    key_map         = array bounds0 [(,) v k                        | (,) v (_,    k, _ ) <- edges1]
    vertex_map      = array bounds0 edges1

    (_,k1,_) `lt` (_,k2,_) = k1 `compare` k2

    key_vertex :: key -> Maybe Vertex
    --  returns Nothing for non-interesting vertices
    key_vertex k   = findVertex 0 max_v
                   where
                     findVertex a b | a > b
                              = Nothing
                     findVertex a b = case compare k (key_map ! mid) of
                                   LT -> findVertex a (mid-1)
                                   EQ -> Just mid
                                   GT -> findVertex (mid+1) b
                              where
                                mid = (a + b) `div` 2

-------------------------------------------------------------------------
--                                                                      -
--      Depth first search
--                                                                      -
-------------------------------------------------------------------------

-- | A spanning forest of the graph, obtained from a depth-first search of
-- the graph starting from each vertex in an unspecified order.
dff          :: Graph e -> [Tree e Vertex]
dff g         = dfs g (vertices g)

-- | A spanning forest of the part of the graph reachable from the listed
-- vertices, obtained from a depth-first search of the graph starting at
-- each of the listed vertices in order.
dfs          :: Graph e -> [Vertex] -> [Tree e Vertex]
dfs g vs      = map dropLabel $ prune (bounds g) (map (\v -> error "dfs: no top-level label" ::> generate g v) vs)

dropLabel :: forall t t1. t ::> t1 -> t1
dropLabel ~(_ ::> t) = t


generate     :: Graph e -> Vertex -> Tree e Vertex
generate g v  = Node v [e ::> generate g v' | (e,v') <- g!v]

prune        :: Bounds -> Forest e Vertex -> Forest e Vertex
prune bnds ts = run bnds (chop ts)

chop         :: Forest e Vertex -> SetM s (Forest e Vertex)
chop []       = return []
chop ((e ::> Node v ts) : us)
              = do
                visited <- contains v
                if visited then
                  chop us
                 else do
                  include v
                  as <- chop ts
                  bs <- chop us
                  return ((e ::> Node v as) : bs)

-- A monad holding a set of vertices visited so far.
-- Use the ST for constant-time primitives.

newtype SetM s a = SetM { runSetM :: STArray s Vertex Bool -> ST s a }

instance Functor (SetM s) where
  fmap f = (pure f <*>)

instance Applicative (SetM s) where
  (<*>) = ap
  pure = return

instance Monad (SetM s) where
    return x     = SetM $ const (return x)
    SetM v >>= f = SetM $ \ s -> do { x <- v s; runSetM (f x) s }

run          :: Bounds -> (forall s. SetM s a) -> a
run bnds act  = runST (newArray bnds False >>= runSetM act)

contains     :: Vertex -> SetM s Bool
contains v    = SetM $ \ m -> readArray m v

include      :: Vertex -> SetM s ()
include v     = SetM $ \ m -> writeArray m v True


-------------------------------------------------------------------------
--                                                                      -
--      Algorithms
--                                                                      -
-------------------------------------------------------------------------

------------------------------------------------------------
-- Algorithm 1: depth first search numbering
------------------------------------------------------------

type DList a = a -> a

dconcat :: [DList a] -> DList a
dconcat = foldr (.) id

preorder' :: [e] -> Tree e a -> DList [(a,[e])]
preorder' es (Node a ts) = ((a,es) :) . preorderF' es ts

preorderF' :: [e] -> Forest e a -> DList [(a,[e])]
preorderF' es ts = dconcat [ preorder' (e : es) t | (e ::> t) <- ts]

preorderF :: [Tree e a] -> [(a,[e])]
preorderF ts = dconcat [ preorder' [] t | t <- ts] []

tabulate        :: Bounds -> [Vertex] -> Table Int
tabulate bnds vs = array bnds (zipWith (,) vs [1..])


preArr          :: Bounds -> [Tree e Vertex] -> Table Int
preArr bnds      = tabulate bnds . map fst . preorderF

------------------------------------------------------------
-- Algorithm 2: topological sorting
------------------------------------------------------------

postorder :: Tree e a -> [a] -> [a]
postorder (Node a ts) = postorderF (map dropLabel ts) . (a :)

postorderF   :: [Tree e a] -> [a] -> [a]
postorderF ts = foldr (.) id $ map postorder ts

postOrd :: Graph e -> [Vertex]
postOrd g = postorderF (dff g) []

-- | A topological sort of the graph.
-- The order is partially specified by the condition that a vertex /i/
-- precedes /j/ whenever /j/ is reachable from /i/ but not vice versa.
topSort      :: Graph e -> [Vertex]
topSort       = reverse . postOrd

------------------------------------------------------------
-- Algorithm 3: connected components
------------------------------------------------------------

-- | The connected components of a graph.
-- Two vertices are connected if there is a path between them, traversing
-- edges in either direction.
components   :: Graph e -> [Tree e Vertex]
components    = dff . undirected

undirected   :: Graph e -> Graph e
undirected g  = buildG (bounds g) (edges g ++ reverseE g)

------------------------------------------------------------
-- Algorithm 4: strongly connected components
------------------------------------------------------------

-- | The strongly connected components of a graph.
scc  :: Graph e -> [Tree e Vertex]
scc g = dfs g (reverse (postOrd (transposeG g)))


------------------------------------------------------------
-- Algorithm 6: Finding reachable vertices
------------------------------------------------------------

-- | A list of vertices reachable from a given vertex.
reachable    :: Graph e -> Vertex -> [(Vertex,[e])]
reachable g v = preorderF (dfs g [v])


-- | Is the second vertex reachable from the first?
path         :: Graph e -> Vertex -> Vertex -> Bool
path g v w    = w `elem` map fst (reachable g v)

-----------------------------------------------------------------
-- Algorithm 7: Biconnected components
------------------------------------------------------------

-- | The biconnected components of a graph.
-- An undirected graph is biconnected if the deletion of any vertex
-- leaves it connected.

bcc :: Graph e -> Forest e [Vertex]
bcc g = (concat . map bicomps . map (do_label g dnum)) forest
 where forest = dff g
       dnum   = preArr (bounds g) forest

do_label :: Graph e -> Table Int -> Tree e Vertex -> Tree e (Vertex,Int,Int)
do_label g dnum (Node v ts) = Node (v,dnum!v,lv) us
 where us = map (fmap (do_label g dnum)) ts
       lv = minimum ([dnum!v] ++ [dnum!w | (e,w) <- g!v]
                     ++ [lu | _ ::> Node (_,_,lu) _ <- us])

bicomps :: Tree e (Vertex,Int,Int) -> Forest e [Vertex]
bicomps (Node (v,_,_) ts)
      = [ e ::> Node (v:vs) us | e ::> (_,Node vs us) <- map (fmap collect) ts]

collect :: Tree e (Vertex,Int,Int) -> (Int, Tree e [Vertex])
collect (Node (v,dv,lv) ts) = (lv, Node (v:vs) cs)
 where collected = map (fmap collect) ts
       vs = concat [ ws | _ ::> (lw, Node ws _) <- collected, lw<dv]
       cs = concat [ if lw<dv then us else [e ::> Node (v:ws) us]
                        | e ::> (lw, Node ws us) <- collected ]
-- * Cycamore stuff

put :: forall s a. STRef s [a] -> a -> ST s ()
put ref item =
 do l <- readSTRef ref
    writeSTRef ref (item:l)

allocId :: forall b s. Num b => STRef s b -> ST s b
allocId uidRef =
    do uid <- readSTRef uidRef
       writeSTRef uidRef (uid + 1)
       return uid

unfoldManyST :: forall key edgeLabel colour stTag. (Ord key) => (key -> (colour, [(edgeLabel, key)]))
             -> [key] -> ST stTag ([Vertex], ColouredGraph colour edgeLabel)
unfoldManyST gen seeds =
     do mtab <- newSTRef M.empty
        allNodes <- newSTRef []
        uidRef <- newSTRef firstId
        let -- cyc :: a -> ST s Vertex
            cyc src =
             do probe <- memTabFind mtab src
                case probe of
                 Just result -> return result
                 Nothing -> do
                     v <- allocId uidRef
                     memTabBind src v mtab
                     let (lab, deps) = gen src
                     ws <- mapM (cyc . snd) deps
                     let res = (v, lab, [(fst d, w) | d <- deps | w <- ws])
                     put allNodes res
                     return v
        mapM_ cyc seeds
        list <- readSTRef allNodes
        seedsResult <- (return . map fromJust) =<< mapM (memTabFind mtab) seeds
        lastId <- readSTRef uidRef
        let cycamore = array (firstId, lastId-1) [(i, k) | (i, a, k) <- list]
        let labels = array (firstId, lastId-1) [(i, a) | (i, a, k) <- list]
        return (seedsResult, ColouredGraph cycamore (labels!))
   where firstId = 0::Vertex
         memTabFind mt key = return . M.lookup key =<< readSTRef mt
         memTabBind key val mt = modifySTRef mt (M.insert key val)

unfold :: forall key edgeLabel colour. (Ord key) => (key -> (colour, [(edgeLabel, key)]))
             -> key -> (Vertex, ColouredGraph colour edgeLabel)
unfold f r = (r', res)
  where ([r'], res) = unfoldMany f [r]

unfoldMany :: forall key edgeLabel colour stTag. (Ord key) => (key -> (colour, [(edgeLabel, key)]))
             -> [key] -> ([Vertex], ColouredGraph colour edgeLabel)
unfoldMany f roots = runST (unfoldManyST f roots)

fold' :: Eq c => c -> (Vertex -> [(b,c)] -> c) -> Graph b -> Vertex -> c
fold' z f gr v = scan' z f gr v

scan' :: Eq c => c -> (Vertex -> [(b,c)] -> c) -> Graph b -> Colouring c
scan' bot f gr = (finalTbl !)
    where finalTbl = fixedPoint updateTbl initialTbl
          initialTbl = listArray bnds (replicate (rangeSize bnds) bot)

          fixedPoint f x = fp x
              where fp z = if z == z' then z else fp z'
                        where z' = f z
          updateTbl tbl = listArray bnds $ map recompute $ vertices gr
              where recompute v = f v [(b, tbl!k) | (b, k) <- gr!v]
          bnds = bounds gr

scan :: Eq c => c -> (a -> [(e,c)] -> c) -> ColouredGraph a e -> ColouredGraph c e
scan bot f (ColouredGraph gr a) = ColouredGraph gr (scan' bot f' gr)
    where f' v kids = f (a v) kids
