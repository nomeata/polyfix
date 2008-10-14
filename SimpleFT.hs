{-# LANGUAGE PatternGuards, FlexibleContexts  #-}

module SimpleFT where

import ParseType
import Expr
import Control.Monad.Reader

test = putStrLn . show . freeTheorem . parseType

freeTheorem t = runReader (freeTheorem' (Var "f") (Var "f") t) freeVars

freeVars = (map (:"") ['a'..])


freeTheorem' :: Expr -> Expr -> Typ -> Reader [String] BoolExpr

freeTheorem' e1 e2 Int = return $
	Equal e1 e2

freeTheorem' e1 e2 (TVar (TypVar i)) = return $
	Equal (App (Var ("g"++show i)) e1) e2

freeTheorem' e1 e2 (Arrow t1 t2) | isTuple t1 = do
	-- Create patterns for (possily nested) tuples and only give
	-- the inner variables names
	fillTuplevars False t1 $ \tve1 -> 
		fillTuplevars True t1 $ \tve2 ->  do
			let ve1 = unTypeExpr tve1
                            ve2 = unTypeExpr tve2
			cond  <- freeTheorem' (ve1) (ve2) t1
			concl <- freeTheorem' (App e1 ve1) (App e2 ve2) t2
			return $ Condition tve1 tve2 cond concl

	-- No tuple on the left hand side:
                                 | otherwise  = getVars 2 $ \[v1,v2] -> do
	cond  <- freeTheorem' (Var v1) (Var v2) t1
	-- See if the variables actually have definitions
	case (defFor v1 cond, defFor v2 cond) of
	  (Just ev1, _) -> do
		concl <- freeTheorem' (App e1 ev1)      (App e2 (Var v2)) t2
		return $ unCond v2 True t1 concl
	  (Nothing,Just ev2) -> do
		concl <- freeTheorem' (App e1 (Var v1)) (App e2 ev2)      t2
		return $ unCond v1 False t1 concl
	  _ -> do
		concl <- freeTheorem' (App e1 (Var v1)) (App e2 (Var v2)) t2
		return $ Condition (typedLeft (Var v1) t1)
                                   (typedRight(Var v2) t1)
                                   cond
                                   concl

freeTheorem' e1 e2 (List t) = getVars 2 $ \[v1,v2] -> do
	map <- freeTheorem' (Var v1) (Var v2) t
	return $ allZipWith v1 v2 map e1 e2

{-
freeTheorem' e1 e2 (TPair t1 t2) = getVars 4 $ \[x1,x2,y1,y2] -> do
	concl1 <- freeTheorem' (Var x1) (Var y1) t1
	concl2 <- freeTheorem' (Var x2) (Var y2) t2
	return $ Condition x1 y1 t1 BETrue $
		 Condition x2 y2 t2 (
			And (Equal e2 (Pair (Var y1) (Var y2)))
			    (Equal e1 (Pair (Var x1) (Var x2)))) $
			And concl1 concl2
-}

freeTheorem' (Pair x1 x2) (Pair y1 y2) (TPair t1 t2) = do
	concl1 <- freeTheorem' x1 y1 t1
	concl2 <- freeTheorem' x2 y2 t2
	return $ And concl1 concl2

freeTheorem' e1 e2 t@(TPair t1 t2) = getVars 4 $ \[x1,x2,y1,y2] -> do
	concl1 <- freeTheorem' (Var x1) (Var y1) t1
	concl2 <- freeTheorem' (Var x2) (Var y2) t2
	return $ unpackPair x1 x2 e1 False t $
			unpackPair y1 y2 e2 True t $
				And concl1 concl2

freeTheorem' e1 e2 (AllStar (TypVar i) t) = TypeVarInst i `fmap` freeTheorem' e1 e2 t
freeTheorem' e1 e2 (All     (TypVar i) t) = TypeVarInst i `fmap` freeTheorem' e1 e2 t

getVars :: (MonadReader [String] m) => Int -> ([String] -> m a) -> m a
getVars n a = asks (take n) >>= local (drop n) . a 

fillTuplevars :: (MonadReader [String] m) => Bool -> Typ -> (TypedExpr -> m a) -> m a
fillTuplevars rightSide t@(TPair t1 t2) a = do
	fillTuplevars rightSide t1 $ \ve1 ->
		fillTuplevars rightSide t2 $ \ve2 ->
			let pair = Pair (unTypeExpr ve1) (unTypeExpr ve2) in
			a (TypedExpr pair t rightSide)
fillTuplevars rightSide t a = getVars 1 $ \[s] ->
			a (TypedExpr (Var s) t rightSide)
	
