{-# LANGUAGE PatternGuards  #-}

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

freeTheorem' e1 e2 (List t) = do
	[v1,v2] <- asks (take 2)
	local (drop 2) $ do
		map <- freeTheorem' (Var v1) (Var v2) t
		return $ allZipWith v1 v2 map e1 e2

freeTheorem' e1 e2 (Arrow t1 t2) = do
	[v1,v2] <- asks (take 2)
	local (drop 2) $ do
		cond  <- freeTheorem' (Var v1) (Var v2) t1
		case (defFor v1 cond, defFor v2 cond) of
	          (Just ev1, _) -> do
			concl <- freeTheorem' (App e1 ev1)      (App e2 (Var v2)) t2
			return $ unCond v2 True t1 concl
	          (Nothing,Just ev2) -> do
			concl <- freeTheorem' (App e1 (Var v1)) (App e2 ev2)      t2
			return $ unCond v1 False t1 concl
		  _ -> do
			concl <- freeTheorem' (App e1 (Var v1)) (App e2 (Var v2)) t2
			return $ Condition v1 v2 t1 cond concl

freeTheorem' e1 e2 (TVar (TypVar i)) = return $
	Equal (App (Var ("g"++show i)) e1) e2

freeTheorem' e1 e2 (AllStar (TypVar i) t) = TypeVarInst i `fmap` freeTheorem' e1 e2 t
freeTheorem' e1 e2 (All     (TypVar i) t) = TypeVarInst i `fmap` freeTheorem' e1 e2 t
