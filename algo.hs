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
        lhs         = srPred l:evalState (unwrap M.empty fi gamma) 0

instance Hashable Refa
instance Hashable Reft
instance Hashable SortedReft

unwrap :: M.HashMap ([BindId],SortedReft,SortedReft) Integer -> FInfo Cinfo -> [(Symbol,SortedReft)] -> State Integer [Pred]
unwrap visited fi binds = mapM unwrap1 (map substBind binds)
  where
    unwrap1 ((sym,sort),p) =
      case p of 
        PKVar kvar subs -> subst subs <$> formula 
          where
            formula        = POr <$> mapM (recur . consTrip fi) cons'
            cons'          = filter undeep $ filter haskv $ M.elems $ cm fi
            undeep       x = depth >= M.lookupDefault 0 (consTri x) visited
            recur  (g,l,_) = PAnd . (srPred l:) <$> unwrap (foldr inc visited $ map consTri cons') fi g
            haskv        c = kvar `elem` (rhsKVars c)
            inc            = flip (M.insertWith (+)) 1
        x -> return x

rename :: Subst -> Pred -> State Integer Pred
rename = undefined
  where alpha sym = state $ (existSymbol sym) &&& (+1)
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

