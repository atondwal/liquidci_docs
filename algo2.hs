module UseInterpolation (useInterpolation) where
import qualified Data.HashMap.Strict as M
import Language.Fixpoint.Solver.Eliminate
import Language.Fixpoint.Types
import Language.Fixpoint.Names (existSymbol)
-- import Language.Liquid.Types
import Language.Fixpoint.Visitor (rhsKVars)

import Data.Hashable
import Control.Arrow
import Control.Monad.State
import Control.Applicative

data Cinfo

interpolate :: Pred -> Pred -> IO Pred
interpolate = undefined

depth :: Integer
depth = undefined

useInterpolation :: FInfo Cinfo -> SubC Cinfo -> IO Pred
useInterpolation fi failCon = interpolate (PAnd lhs) rhs
  where (gamma,l,r) = consTrip fi failCon
        rhs         = PNot $ srPred r
        lhs         = srPred l:map (snd.substBind) gamma

type Miii = (M.HashMap Integer Integer, Integer)

-- unrolls all of the constraints into nice, flat graph we can `eliminate`
unroll :: FInfo Cinfo -> [(Symbol,SortedReft)] -> FInfo Cinfo
unroll = ((.).(.)) evalState unwrap

-- like the above, but some state tags along
unwrap :: FInfo Cinfo -> [(Symbol,SortedReft)] -> State Miii (FInfo Cinfo)
unwrap = foldM (unwrap1.srPred.snd)


unwrap1 :: FInfo Cinfo -> (Symbol,SortedReft) -> State Miii (FInfo Cinfo)
unwrap1 fi (PKVar kvar _) = let haskv     c = kvar `elem` (rhsKVars c)
                             in do cons <- join <$> sequence $ M.mapWithKey undeep $ M.filter haskv $ cm fi
                                   -- cons :: [(Integer, SubC Cinfo)]
                                   modify $ first (update cs)
                                   return $ fi { cm = foldl' (\m (k,v) -> insert m k v) (cm x) cons }
                                >>= foldM (\x -> unwrap x . gamma x) fi cons'
unwrap1 fi _ = return fi

update :: [(a,b)] -> M.HashMap a Integer -> M.HashMap a Integer
update cs v = foldl inc v $ map fst cs
  where inc    m  k = M.insertWith (+) k 1 m

-- unrolls just one constraint if it needs to be
undeep :: Integer -> SubC a -> State Miii [SubC a]
undeep x c = do
  (visited,counter) <- get
  if depth >= M.lookupDefault 0 x visited
     then splitk c >>= \(newk, r, l) ->
          [(x,r),(counter+fromIntegral $ size visited,l)]
     else return [(x,trivialize c)]

splitk :: SubC a -> State Miii (SubC a)
splitk c@(SubC _ _ _ (RR rr (Reft (sym,Refa (PKVar k)))) _ _ a) = do
  modify (+1)
  counter <- get
  let newk = rename k counter in (newk,c { rhs  = (RR rr (Reft (sym,Refa (PKVar newk)))) },

trivialize :: SubC a -> SubC a
trivialize c = c { srhs = wipe srhs }
  where wipe (RR sort (Reft (sym, _))) = RR sort $ Reft (sym, PTrue)

gamma :: FInfo a -> SubC a -> [(Symbol, SortedReft)]
gamma fi c = map (\m -> lookupBindEnv m (bs fi)) $ elemsIBindEnv $ senv c

rename :: Subst -> Pred -> State Integer Pred
rename = undefined
  where alpha sym = state $ (existSymbol sym) &&& (second (+1))
-- rename free f = applySubs subs f
--   where bound = filterF (`notElem` free) f
--         subs  = M.fromList $ map ((,) fresh) bound
--         fresh = undefined

srPred :: SortedReft -> Pred
srPred = reftPred . sr_reft

consTrip :: FInfo Cinfo -> SubC Cinfo -> ([(Symbol,SortedReft)],SortedReft,SortedReft)
consTrip fi c = (gamma, l, r)
  where (l,r) = (srhs &&& slhs) c
        igamma = elemsIBindEnv $ senv c
        gamma = map (\m -> lookupBindEnv m (bs fi)) igamma

consTri :: SubC Cinfo -> ([BindId],SortedReft,SortedReft)
consTri c = (igamma, l, r)
  where (l,r) = (srhs &&& slhs) c
        igamma = elemsIBindEnv $ senv c

