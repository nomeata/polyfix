{-# LANGUAGE PatternGuards  #-}
module Expr where

import Data.List
import ParseType

data Expr
	= Var String
	| App Expr Expr
	| Conc [Expr] -- Conc [] is Id
	| Lambda String Expr
	| Map
            deriving (Eq)

data BoolExpr 
	= Equal Expr Expr
	| Pairwise String String BoolExpr Expr Expr
	| Condition String String Typ BoolExpr BoolExpr
	| UnCond String Bool Typ BoolExpr
	| TypeVarInst Int BoolExpr
            deriving (Eq)

-- Smart constructors

equal = Equal

pairwise v1 v2 rel e1 e2 | Just v1' <- defFor v1 rel =
				e1 `equal` app (app Map (lambda v2 v1')) e2
                         | Just v2' <- defFor v2 rel =
				app (app Map (lambda v1 v2')) e1 `equal` e2
                         | otherwise =
				Pairwise v1 v2 rel e1 e2

defFor v (e1 `Equal` e2) | (Var v) == e1 = Just e2
                         | (Var v) == e2 = Just e1
defFor _ _                               = Nothing

app Map (Conc []) = Conc []
app (Conc []) v   = v
app f v           = App f v

unCond v b t (Equal l r) | (Just l') <- isApplOn v l 
	                 , (Just r') <- isApplOn v r = 
	if hasVar v l' || hasVar v r'
	then UnCond v b t (Equal l' r')
	else (Equal l' r')
unCond v b t e = UnCond v b t e

lambda v e | (Just e') <- isApplOn v e, not (hasVar v e') = e'
	   | Var v == e                                   = Conc []
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
hasVar v (Lambda _ e) = hasVar v e
hasVar v Map          = False


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
	showsPrec d (Conc [])   = showString "id"
	showsPrec d (Conc [e])  = showsPrec d e
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
				showString "\\" .
				showString v1 .
				showChar ' ' .
				showString v2 . 
				showString " -> " .
				showsPrec 0 be
			) .
			showChar ' ' .
			showsPrec 11 e1 .
			showChar ' ' .
			showsPrec 11 e2
	showsPrec d (Condition v1 v2 t be1 be2) = 
			showParen (d>6) $
			showString "forall " . 
			showString v1 . 
			showString " :: " .
			arrowInstType False t .
			showString ", " .
			showString v2 . 
			showString " :: " .
			arrowInstType True t .
			showString ".\n" .
			showsPrec 9 be1 .
			showString " ==> " .
			showsPrec 6 be2
	showsPrec d (UnCond v1 b t be1) = 
			showParen (d>6) $
			showString "forall " . 
			showString v1 . 
			showString " :: " .
			arrowInstType b t .
			showString ".\n" .
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

arrowInstType :: Bool -> Typ -> ShowS
arrowInstType b Int			= showString "Int" 
arrowInstType False (TVar (TypVar i))	= showString "t" .  shows (2*i-1)
arrowInstType True (TVar (TypVar i))	= showString "t" .  shows (2*i)
arrowInstType b (Arrow t1 t2)    	= arrowInstType b t1 .
					  showString " -> " .
					  arrowInstType b t2
