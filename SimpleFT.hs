{-# LANGUAGE PatternGuards, FlexibleContexts  #-}

module SimpleFT where

import ParseType
import Expr
import Control.Monad.Reader

test = putStrLn . show . freeTheorem . parseType

freeTheorem t = flip runReader freeVars $ 
			freeTheorem' (typedLeft  (Var "f") (unquantify t))
				     (typedRight (Var "f") (unquantify t))
                                     t
freeVars = (map (:"") ['a'..])


freeTheorem' :: TypedExpr -> TypedExpr -> Typ -> Reader [String] BoolExpr

freeTheorem' e1 e2 Int = return $
	equal e1 e2

freeTheorem' e1 e2 (TVar (TypVar i)) = return $
	let tv = TypedExpr (Var ("g"++show i))
                           (Arrow (TVar (TypInst i False)) (TVar (TypInst i True)))
	in equal (app tv e1) e2

freeTheorem' e1 e2 (Arrow t1 t2) | isTuple t1 = do
	-- Create patterns for (possily nested) tuples and only give
	-- the inner variables names
	fillTuplevars False t1 $ \tve1 -> 
		fillTuplevars True t1 $ \tve2 ->  do
			cond  <- freeTheorem' (tve1) (tve2) t1
			concl <- freeTheorem' (app e1 tve1) (app e2 tve2) t2
			return $ condition [tve1, tve2] cond concl

	-- No tuple on the left hand side:
                                 | otherwise  = getSideVars t1 $ \(v1,v2) -> do
	cond  <- freeTheorem'  v1  v2 t1
	concl <- freeTheorem' (app e1  v1) (app e2  v2) t2
	return $ condition [ v1, v2 ] cond concl

freeTheorem' e1 e2 (List t) = getSideVars t $ \(v1,v2) -> do
	map <- freeTheorem' v1 v2 t
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

freeTheorem' e1 e2 t@(TPair t1 t2) 
	| (Pair   x1  x2) <- unTypeExpr e1
	, (Pair   y1  y2) <- unTypeExpr e2
	   = do concl1 <- freeTheorem' 
			(TypedExpr x1 tx1)
			(TypedExpr y1 ty1)
			t1
		concl2 <- freeTheorem'
			(TypedExpr x2 tx2)
			(TypedExpr y2 ty2)
			t2
		return $ aand concl1 concl2
	| otherwise
	   = getVars 4 $ \[x1',x2',y1',y2'] -> do
		let x1 = TypedExpr (Var x1') tx1
		    x2 = TypedExpr (Var x2') tx2
		    y1 = TypedExpr (Var y1') ty1
		    y2 = TypedExpr (Var y2') ty2
		concl1 <- freeTheorem' x1 y1 t1
		concl2 <- freeTheorem' x2 y2 t2
		return $ unpackPair x1 x2 e1 $
				unpackPair y1 y2 e2  $
					aand concl1 concl2
 where (TPair tx1 tx2) = typeOf e1
       (TPair ty1 ty2) = typeOf e2

freeTheorem' e1 e2 (AllStar (TypVar i) t) = TypeVarInst i `fmap` freeTheorem' e1 e2 t
freeTheorem' e1 e2 (All     (TypVar i) t) = TypeVarInst i `fmap` freeTheorem' e1 e2 t

getVars :: (MonadReader [String] m) => Int -> ([String] -> m a) -> m a
getVars n a = asks (take n) >>= local (drop n) . a 

getSideVars :: (MonadReader [String] m) => Typ -> ((TypedExpr,TypedExpr) -> m a) -> m a
getSideVars t a = getVars 2 $ \[v1,v2] -> a (typedLeft (Var v1) t, typedRight (Var v2) t)

fillTuplevars :: (MonadReader [String] m) => Bool -> Typ -> (TypedExpr -> m a) -> m a
fillTuplevars rightSide t@(TPair t1 t2) a = do
	fillTuplevars rightSide t1 $ \ve1 ->
		fillTuplevars rightSide t2 $ \ve2 ->
			let pair = Pair (unTypeExpr ve1) (unTypeExpr ve2) in
			a (TypedExpr pair (instType rightSide t))
fillTuplevars rightSide t a = getVars 1 $ \[s] ->
			a (TypedExpr (Var s) (instType rightSide t))
	
