{-# LANGUAGE PatternGuards, FlexibleContexts  #-}

module SimpleFT where

import ParseType
import Expr
import Control.Monad.Reader
import Data.List

test :: String -> IO ()
test = putStrLn . show . freeTheorem . parseType

freeTheorem :: Typ -> BoolExpr
freeTheorem t = flip runReader freeVars $ 
			freeTheorem' (typedLeft  (Var F) (unquantify t))
				     (typedRight (Var F) (unquantify t))
                                     t
freeVars :: [Int]
freeVars = [1..]


freeTheorem' :: (MonadReader [Int] m) => TypedExpr -> TypedExpr -> Typ -> m BoolExpr

freeTheorem' e1 e2 Int = return $
	equal e1 e2

freeTheorem' e1 e2 (TVar (TypVar i)) = return $
	let tv = TypedExpr (Var (FromTypVar i))
                           (Arrow (TVar (TypInst i False)) (TVar (TypInst i True)))
	in equal (app tv e1) e2

freeTheorem' e1 e2 (Arrow t1 t2) = getSideVars t1 $ \(v1,v2) -> do
	cond  <- freeTheorem'  v1  v2 t1
	concl <- freeTheorem' (app e1  v1) (app e2  v2) t2
	return $ condition [ v1, v2 ] cond concl

freeTheorem' e1 e2 (List t) = getSideVars t $ \(v1,v2) -> do
	mapRel <- freeTheorem' v1 v2 t
	return $ allZipWith v1 v2 mapRel e1 e2

freeTheorem' e1 e2 (TEither t1 t2) = do
	rel1 <- genRel t1
	rel2 <- genRel t2
	return $ andEither rel1 rel2 e1 e2

freeTheorem' e1 e2 (TPair t1 t2) 
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
	   = getVars 2 $ \[v1,v2] -> do
		let x1 = TypedExpr (Var (FromParam v1 False)) tx1
		    x2 = TypedExpr (Var (FromParam v2 False)) tx2
		    y1 = TypedExpr (Var (FromParam v1 True)) ty1
		    y2 = TypedExpr (Var (FromParam v2 True)) ty2
		concl1 <- freeTheorem' x1 y1 t1
		concl2 <- freeTheorem' x2 y2 t2
		return $ unpackPair x1 x2 e1 $
				unpackPair y1 y2 e2  $
					aand concl1 concl2
 where (TPair tx1 tx2) = typeOf e1
       (TPair ty1 ty2) = typeOf e2

freeTheorem' e1 e2 (AllStar (TypVar i) t) = TypeVarInst True i `liftM` freeTheorem' e1 e2 t
freeTheorem' e1 e2 (All     (TypVar i) t) = TypeVarInst False i `liftM` freeTheorem' e1 e2 t

freeTheorem' _ _ t = error $ "Type " ++ show t ++ " passed to freeTheorem'"

genRel :: (MonadReader [Int] m) => Typ -> m LambdaBE
genRel t = getSideVars t $ \(v1,v2) -> do
		mapRel <- freeTheorem' v1 v2 t
		return $ lambdaBE v1 v2 mapRel

getVars :: (MonadReader [Int] m) => Int -> ([Int] -> m a) -> m a
getVars n a = asks (take n) >>= local (drop n) . a 

getSideVars :: (MonadReader [Int] m) => Typ -> ((TypedExpr,TypedExpr) -> m a) -> m a
getSideVars t a = getVars 1 $ \[v] ->
		a (typedLeft  (Var (FromParam v False)) t,
                   typedRight (Var (FromParam v True))  t)
