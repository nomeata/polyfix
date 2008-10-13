{-# LANGUAGE PatternGuards  #-}
module Expr where

import Data.List

data Expr
	= Var String
	| App Expr Expr
	| Conc [Expr]
	| Lambda String Expr
	| Map
            deriving (Eq)

data BoolExpr 
	= Equal Expr Expr
	| Pairwise String String BoolExpr Expr Expr
	| Condition String String BoolExpr BoolExpr
	| UnCond String BoolExpr
	| TypeVarInst Int BoolExpr
            deriving (Eq)

-- Smart constructors

unCond v (Equal l r) | (Just l') <- isApplOn v l 
	             , (Just r') <- isApplOn v r = 
	if hasVar v l' || hasVar v r'
	then UnCond v (Equal l' r')
	else (Equal l' r')
unCond v e = UnCond v e

lambda v e | (Just e') <- isApplOn v e, not (hasVar v e') = e'
           | otherwise                                    = Lambda v e


conc f (Conc fs) = Conc (f:fs)

-- Helpers

isApplOn v (Var _)                                         = Nothing
isApplOn v (App f (Var v')) | v == v'                      = Just (Conc [f])
isApplOn v (App f e)        | (Just inner) <- isApplOn v e = Just (conc f inner)
isApplOn _ _                                               = Nothing

hasVar v (Var v')     = v == v'
hasVar v (App e1 e2)  = hasVar v e1 && hasVar v e2
hasVar v (Conc es)    = any (hasVar v) es


-- showing

-- Precedences:
-- 10 fun app
--  9 (.)
--  8 ==
--  7 ==>
--  6 forall

instance Show Expr where
	showsPrec d (Var s)     = showString s
	showsPrec d (App e1 e2) = showParen (d>10) $
		showsPrec 10 e1 . showChar ' ' . showsPrec 11 e2
	showsPrec d (Conc es)   = showParen (d>9) $
		showIntercalate (showString " . ") (map (showsPrec 10) es)
	showsPrec d (Lambda v e) = showParen True $ 
				   showString "\\" .
                                   showString v .
                                   showString " -> ".
			           showsPrec 0 e 
	showsPrec _ Map           = showString "map"

showIntercalate i []  = id
showIntercalate i [x] = x
showIntercalate i (x:xs) = x . i . showIntercalate i xs

instance Show BoolExpr where
	showsPrec d (Equal e1 e2) = showParen (d>8) $
				    showsPrec 9 e1 .
				    showString " == " .
				    showsPrec 9 e2 
	showsPrec d (Pairwise v1 v2 be e1 e2) =
			showParen (d>10) $
			showString "allZipWith " .
			showParen True ( 
				showString "(\\" .
				showString v1 .
				showChar ' ' .
				showString v2 . 
				showString " -> " .
				showsPrec 0 e1
			) .
			showChar ' ' .
			showsPrec 11 e2
	showsPrec d (Condition v1 v2 be1 be2) = 
			showParen (d>6) $
			showString "forall " . 
			showString v1 . 
			showChar ' ' .
			showString v2 . 
			showString ". " .
			showsPrec 9 be1 .
			showString " ==> " .
			showsPrec 6 be2
	showsPrec d (UnCond v1 be1) = 
			showParen (d>6) $
			showString "forall " . 
			showString v1 . 
			showString ". " .
			showsPrec 6 be1
	showsPrec d (TypeVarInst i be) = 
			showParen (d>6) $
			showString "forall types t" .
			shows (2*i-1) .
			showString ", t" .
			shows (2*i) . 
			showString ", function g" .
			shows i .
			showString " :: t" .
			shows (2*i-1) .
			showString " -> t" .
			shows (2*i) . 
			showString ".\n" .
			showsPrec 6 be

