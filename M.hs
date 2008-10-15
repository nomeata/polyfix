module M (M,runM,newInt,newAux,choice,abort,runMAll,track) where

type State = (Int,Int,[String])

data M a = M (State -> [(a,State)])

instance Monad M where
    return a = M (\s -> [(a,s)])
    M m >>= k = M (\s -> concatMap (\(a,s') -> case k a of M l -> l s') (m s))

runM :: M a -> Maybe (a, [String])
runM (M m) = case m (1,0,[]) of
	       []        -> Nothing
	       ((a,(_,_,ls)):_) -> Just (a,reverse ls)

runMAll :: M a -> [(a, [String])]
runMAll (M m) = map (\(a,(_,_,ls)) -> (a,reverse ls)) (m (1,0,[]))

newInt :: M Int
newInt = M (\(i,j,ls) -> [(i,(i+1,j,ls))])

newAux :: M Int
newAux = M (\(i,j,ls) -> [(j,(i,j-1,ls))])

choice :: M a -> M a -> M a
choice (M m) (M l) = M (\s -> m s ++ l s)

abort :: M a
abort = M (\s -> [])

track :: String -> M ()
track l = M (\(i,j,ls) -> [((),(i,j,l:ls))])
