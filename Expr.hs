{-# LANGUAGE PatternGuards  #-}
module Expr where

import Data.List
import ParseType

data TypedExpr = TypedExpr
	{ unTypeExpr	:: Expr
	, typeOf	:: Typ
	, onRightSide	:: Bool
	} deriving (Eq)

data Expr
	= Var String
	| App Expr Expr
	| Conc [Expr] -- Conc [] is Id
	| Lambda String Expr
	| Pair Expr Expr
	| Map
            deriving (Eq)

data BoolExpr 
	= BETrue
	| Equal Expr Expr
	| And BoolExpr BoolExpr
	| AllZipWith String String BoolExpr Expr Expr
	| Condition TypedExpr TypedExpr  BoolExpr BoolExpr
	| UnpackPair String String Expr Bool Typ BoolExpr
	| UnCond String Bool Typ BoolExpr
	| TypeVarInst Int BoolExpr
            deriving (Eq)

-- Smart constructors

-- Left or right side of a relation (affects type variables)
typedLeft e t = TypedExpr e t False
typedRight e t = TypedExpr e t True

equal = Equal

unpackPair = UnpackPair

allZipWith v1 v2 rel e1 e2 | Just v1' <- defFor v1 rel =
				e1 `equal` app (app Map (lambda v2 v1')) e2
                           | Just v2' <- defFor v2 rel =
				app (app Map (lambda v1 v2')) e1 `equal` e2
                           | otherwise =
				AllZipWith v1 v2 rel e1 e2

-- | Is inside the term a definition for the variable?
defFor v (e1 `Equal` e2) | (Var v) == e1 = Just e2
                         | (Var v) == e2 = Just e1
defFor v (e1 `And` e2)   | Just d  <- defFor v e1
		         , Nothing <- defFor v e2 = Just d
defFor v (e1 `And` e2)   | Just d  <- defFor v e2
		         , Nothing <- defFor v e1 = Just d
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

isTuple (TPair _ _) = True
isTuple _           = False


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
	showsPrec _ (Pair e1 e2) = showParen True $ 
			           showsPrec 0 e1 .
				   showString "," .
			           showsPrec 0 e2
	showsPrec _ Map           = showString "map"

showIntercalate i []  = id
showIntercalate i [x] = x
showIntercalate i (x:xs) = x . i . showIntercalate i xs

instance Show TypedExpr where
	showsPrec d (TypedExpr e t rightSide) = 
		showParen (d>10) $
			showsPrec 0 e .
			showString " :: " .
			showString (arrowInstType rightSide t)

instance Show BoolExpr where
	show (Equal e1 e2) = showsPrec 9 e1 $
			     showString " == " $
			     showsPrec 9 e2 ""
	show (And be1 be2) = show be1 ++
			     " && " ++
			     show be2 
	show (AllZipWith v1 v2 be e1 e2) =
			"allZipWith " ++
			"( " ++
			"\\" ++
			v1 ++
			" " ++
			v2 ++
			" -> " ++
			show be ++
			")" ++
			" " ++
			showsPrec 11 e1 "" ++
			" " ++
			showsPrec 11 e2 ""
	show (Condition tv1 tv2 be1 be2) = 
			"forall " ++
			showsPrec 0 tv1 "" ++
			", " ++
			showsPrec 0 tv2 "" ++
			".\n" ++
			(if be1 /= BETrue then indent 2 (show be1) ++ "==>\n" else "") ++
			indent 2 (show be2)
	show (UnpackPair v1 v2 e b t be) = 
			"let (" ++
			v1 ++
			"," ++
			v2 ++
			") = " ++
			showsPrec 0 e "" ++
			" :: " ++
			arrowInstType b t ++
			" in\n" ++
			indent 2 (show be)
	show (UnCond v1 b t be1) = 
			"forall " ++
			v1 ++
			" :: " ++
			arrowInstType b t ++
			".\n" ++
			indent 2 (show be1)
	show (TypeVarInst i be) = 
			"forall types t" ++
			show (2*i-1) ++
			", t" ++
			show (2*i) ++
			", function g" ++
			show i ++
			" :: t" ++
			show (2*i-1) ++
			" -> t" ++
			show (2*i) ++ 
			".\n" ++
			indent 2 (show be)

indent n = unlines . map (replicate n ' ' ++) . lines

arrowInstType :: Bool -> Typ -> String
arrowInstType b = ait 0
  where 
	ait _ Int			= "Int" 
	ait _ (TVar (TypVar i)) | not b	= "t" ++  show (2*i-1)
                                |     b = "t" ++  show (2*i)
	ait d (Arrow t1 t2)    		= paren (d>9) $ 
						  ait 10 t1 ++ " -> " ++ ait 9 t2 
	ait d (List t)          	= "[" ++ ait 0 t ++ "]"
	ait d (TEither t1 t2)        	= "Either " ++ ait 11 t1 ++ 
                                                " " ++ ait 11 t2
	ait d (TPair t1 t2)        	= "(" ++ ait 0 t1 ++ "," ++ ait 0 t2 ++ ")"

paren b p   =  if b then "(" ++ p ++ ")" else p
