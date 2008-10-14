{-# LANGUAGE PatternGuards, DeriveDataTypeable   #-}
module Expr where

import Data.List
import ParseType

import Data.Generics hiding (typeOf)
import Data.Generics.Schemes

data TypedExpr = TypedExpr
	{ unTypeExpr	:: Expr
	, typeOf	:: Typ
	} deriving (Eq, Typeable, Data)

typedLeft, typedRight :: Expr -> Typ -> TypedExpr
typedLeft  e t = TypedExpr e (instType False t)
typedRight e t = TypedExpr e (instType True t)

data Expr
	= Var String
	| App Expr Expr
	| Conc [Expr] -- Conc [] is Id
	| Lambda TypedExpr Expr
	| Pair Expr Expr
	| Map
            deriving (Eq, Typeable, Data)

data BoolExpr 
	= BETrue
	| Equal Expr Expr
	| And BoolExpr BoolExpr
	| AllZipWith TypedExpr TypedExpr BoolExpr Expr Expr
	| Condition [TypedExpr] BoolExpr BoolExpr
	| UnpackPair TypedExpr TypedExpr TypedExpr BoolExpr
	| TypeVarInst Int BoolExpr
            deriving (Eq, Typeable, Data)

-- Smart constructors

equal te1 te2 | typeOf te1 /= typeOf te2 = error "Type mismatch in equal"
              | otherwise                = Equal (unTypeExpr te1) (unTypeExpr te2)

unpackPair = UnpackPair

allZipWith v1 v2 rel e1 e2 | Just v1' <- defFor v1 rel =
				e1 `equal` amap (lambda v2 v1') e2
                           | Just v2' <- defFor v2 rel =
				amap (lambda v1 v2') e1 `equal` e2
                           | otherwise =
				AllZipWith v1 v2 rel (unTypeExpr e1) (unTypeExpr e2)

amap tf tl | Arrow t1 t2 <- typeOf tf
           , List t      <- typeOf tl
           , t1 == t
           = let tMap = TypedExpr Map (Arrow (List t1) (List t2))
	     in app (app tMap tf) tl
amap tf tl | otherwise = error "Type error in map"

-- | Is inside the term a definition for the variable?
defFor :: TypedExpr -> BoolExpr -> Maybe TypedExpr
defFor tv be | Just e' <- defFor' (unTypeExpr tv) be
                         = Just (TypedExpr e' (typeOf tv))
             | otherwise = Nothing
	
defFor' v (e1 `Equal` e2) | v == e1                 = Just e2
                          | v == e2                 = Just e1
defFor' v (e1 `And` e2)   | Just d  <- defFor' v e1
		          , Nothing <- defFor' v e2 = Just d
defFor' v (e1 `And` e2)   | Just d  <- defFor' v e2
		          , Nothing <- defFor' v e1 = Just d
defFor' _ _                                         = Nothing

app te1 te2 | Arrow t1 t2 <- typeOf te1
	    , t3          <- typeOf te2 
            , t1 == t3 
            = TypedExpr (app' (unTypeExpr te1) (unTypeExpr te2)) t2
 where app' Map (Conc []) = Conc []
       app' (Conc []) v   = v
       app' f v           = App f v
app te1 te2 | otherwise                          = error $ "Type mismatch in app: " ++
                                                           show te1 ++ " " ++ show te2

unCond v (Equal l r) | (Just l') <- isApplOn (unTypeExpr v) l 
	             , (Just r') <- isApplOn (unTypeExpr v) r = 
	if v `occursIn` l' || v `occursIn` r'
	then Condition [v] BETrue (Equal l' r')
	else (Equal l' r')
unCond v e = Condition [v] BETrue e

lambda tv e = TypedExpr inner (Arrow (typeOf tv) (typeOf e))
  where inner | (Just e') <- isApplOn (unTypeExpr tv) (unTypeExpr e)
	      , not (unTypeExpr tv `occursIn` e')
                          = e'
	      | tv == e   = Conc []
              | otherwise = Lambda tv (unTypeExpr e)

conc f (Conc fs) = Conc (f:fs)

-- Helpers

isApplOn e e'         | e == e'                       = Nothing
isApplOn e (App f e') | e == e'                       = Just (Conc [f])
isApplOn e (App f e') | (Just inner) <- isApplOn e e' = Just (conc f inner)
isApplOn _ _                                          = Nothing

hasVar v (Var v')     = v == v'
hasVar v (App e1 e2)  = hasVar v e1 && hasVar v e2
hasVar v (Conc es)    = any (hasVar v) es
hasVar v (Lambda _ e) = hasVar v e
hasVar v Map          = False

e `occursIn` e'       = not (null (listify (==e) e'))

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
	showsPrec d (Lambda tv e) = showParen True $ 
				    showString "\\" .
                                    showsPrec 0 tv .
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
	showsPrec d (TypedExpr e t) = 
		showParen (d>10) $
			showsPrec 0 e .
			showString " :: " .
			showString (showTypePrec 0 t)

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
			showsPrec 11 v1 "" ++
			" " ++
			showsPrec 11 v2 "" ++
			" -> " ++
			show be ++
			")" ++
			" " ++
			showsPrec 11 e1 "" ++
			" " ++
			showsPrec 11 e2 ""
	show (Condition tvars be1 be2) = 
			"forall " ++
			intercalate ", " (map show tvars) ++
			".\n" ++
			(if be1 /= BETrue then indent 2 (show be1) ++ "==>\n" else "") ++
			indent 2 (show be2)
	show (UnpackPair v1 v2 e be) = 
			"let (" ++
			showsPrec 0 v1 "" ++
			"," ++
			showsPrec 0 v2 "" ++
			") = " ++
			showsPrec 0 e "" ++
			" in\n" ++
			indent 2 (show be)
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

showTypePrec :: Int -> Typ -> String
showTypePrec _ Int			    = "Int" 
showTypePrec _ (TVar (TypVar i))            = "a"++show i
showTypePrec _ (TVar (TypInst i b)) | not b = "t" ++  show (2*i-1)
	      		            |     b = "t" ++  show (2*i)
showTypePrec d (Arrow t1 t2)                = paren (d>9) $ 
				  showTypePrec 10 t1 ++ " -> " ++ showTypePrec 9 t2 
showTypePrec d (List t)          	    = "[" ++ showTypePrec 0 t ++ "]"
showTypePrec d (TEither t1 t2)        	    = "Either " ++ showTypePrec 11 t1 ++ 
					            " " ++ showTypePrec 11 t2
showTypePrec d (TPair t1 t2)        	    = "(" ++ showTypePrec 0 t1 ++
                                              "," ++ showTypePrec 0 t2 ++ ")"

paren b p   =  if b then "(" ++ p ++ ")" else p
