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
		case map of
		  (Equal (Var v1') ev1) | v1' == v1 -> do
			return $ Equal e1 (App (App (Var "map") (lambda v2 ev1)) e2)
		  _ -> do
			return $ Pairwise v1 v2 map e1 e2

freeTheorem' e1 e2 (Arrow t1 t2) = do
	[v1,v2] <- asks (take 2)
	local (drop 2) $ do
		cond  <- freeTheorem' (Var v1) (Var v2) t1
		case cond of
		  (Equal (Var v1') ev1) | v1' == v1 -> do
			concl <- freeTheorem' (App e1 ev1) (App e2 (Var v2)) t2
			return $ unCond v2 concl
		  _ -> do
			concl <- freeTheorem' (App e1 (Var v1)) (App e2 (Var v2)) t2
			return $ Condition v1 v2 cond concl

freeTheorem' e1 e2 (TVar (TypVar i)) = return $
	Equal e1 (App (Var ("g"++show i)) e2)

freeTheorem' e1 e2 (AllStar (TypVar i) t) = TypeVarInst i `fmap` freeTheorem' e1 e2 t
freeTheorem' e1 e2 (All     (TypVar i) t) = TypeVarInst i `fmap` freeTheorem' e1 e2 t
