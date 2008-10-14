{-# LANGUAGE PatternGuards, DeriveDataTypeable   #-}
module Expr where

import Data.List
import Data.Maybe
import ParseType

import Debug.Trace

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
	= Equal Expr Expr
	| And [BoolExpr] -- And [] is True
	| AllZipWith TypedExpr TypedExpr BoolExpr Expr Expr
	| Condition [TypedExpr] BoolExpr BoolExpr
	| UnpackPair TypedExpr TypedExpr TypedExpr BoolExpr
	| TypeVarInst Int BoolExpr
            deriving (Eq, Typeable, Data)

-- Smart constructors

-- | Try eta reduction
equal te1 te2 | typeOf te1 /= typeOf te2 = error "Type mismatch in equal"
              | otherwise                = equal' (unTypeExpr te1) (unTypeExpr te2)

equal' e1 e2  | (Just (lf,lv)) <- isFunctionApplication e1
              , (Just (rf,rv)) <- isFunctionApplication e2
              , lv == rv 
	                                 = equal' lf rf
	      -- This makes it return True...
	      | e1 == e2                 = beTrue
              | otherwise                = Equal e1 e2

isFunctionApplication (App f e') | (Just (inner,v)) <- isFunctionApplication e'
                                 = Just (conc f inner, v)
                                 | otherwise
                                 = Just (f, e')
isFunctionApplication _          = Nothing


-- | If both bound variables are just functions, we can replace this
--   by a comparison
unpackPair v1 v2 te be | Just subst1 <- findReplacer v1 be
                       , Just subst2 <- findReplacer v2 be
		       = subst1. subst2 $ (pair v1 v2 `equal` te) `aand` be

-- | If the whole tuple is a function, we can replace this
--   by a comparison
unpackPair v1 v2 te be | Just subst <- findReplacer (pair v1 v2) be
		       = subst $ (pair v1 v2 `equal` te) `aand` be

-- | Nothing to optimize
unpackPair v1 v2 te be = UnpackPair v1 v2 te be

pair (TypedExpr e1 t1) (TypedExpr e2 t2) = TypedExpr (Pair e1 e2) (TPair t1 t2)

allZipWith :: TypedExpr -> TypedExpr -> BoolExpr -> TypedExpr -> TypedExpr -> BoolExpr
allZipWith v1 v2 rel e1 e2 | Just v1' <- defFor v1 rel =
				e1 `equal` amap (lambda v2 v1') e2
                           | Just v2' <- defFor v2 rel =
				amap (lambda v1 v2') e1 `equal` e2
                           | otherwise =
				AllZipWith v1 v2 rel (unTypeExpr e1) (unTypeExpr e2)

amap tf tl | Arrow t1 t2 <- typeOf tf
           , List t      <- typeOf tl
           , t1 == t
           = let tMap = TypedExpr Map (Arrow (Arrow t1 t2) (Arrow (List t1) (List t2)))
	     in app (app tMap tf) tl
amap tf tl | otherwise = error "Type error in map"

aand (And xs) (And ys) = And (xs  ++ ys)
aand (And xs) y        = And (xs  ++ [y])
aand x        (And ys) = And ([x] ++ ys)
aand x        y        = And ([x,y])

beTrue = And []

-- | Optimize a forall condition
condition :: [TypedExpr] -> BoolExpr -> BoolExpr -> BoolExpr
-- empty condition
condition [] cond concl   | cond == beTrue
                          = concl
-- float out conditions on the right
condition vars cond (Condition vars' cond' concl')
			  = condition (vars ++ vars') (cond `aand` cond') concl'

-- Try to find variables that are functions of other variables, and remove them
condition vars cond concl | True -- set to false to disable
                          , ((vars',cond',concl'):_) <- mapMaybe try vars
			  = condition vars' cond' concl'
              -- A variable which can be replaced
  where try v | Just subst <- findReplacer v cond
              = -- trace ("Tested " ++ show v ++ ", can be replaced") $
                Just (delete v vars, subst cond, subst concl)
 
	      -- A variable with can be removed
              | not (unTypeExpr v `occursIn` cond || unTypeExpr v `occursIn` concl)
              = -- trace ("Tested " ++ show v ++ ", can be reased") $
                Just (delete v vars, cond, concl)

              -- Nothing to do with this variable
              | otherwise
              = -- trace ("Tested " ++ show v ++ " without success") $
                Nothing

-- Nothing left to optizmize
condition vars cond concl = Condition vars cond concl

-- | Replaces a Term in a BoolExpr
replaceTermBE :: Expr -> Expr -> BoolExpr -> BoolExpr
replaceTermBE d r = go
  where go (e1 `Equal` e2) | d == e1 && r == e2 = beTrue
                           | d == e2 && r == e1 = beTrue
                           | otherwise          = go' e1 `equal'` go' e2
        go (And es)        = foldr aand beTrue (map go es)
        go (AllZipWith v1 v2 be e1 e2) 
                           = AllZipWith v1 v2 (go be) (go' e1) (go' e2)
	go (Condition vs cond concl)
			   = condition vs (go cond) (go concl)
	go (UnpackPair v1 v2 e be)
			   = unpackPair v1 v2 (go' e) (go be)
	go (TypeVarInst _ _) = error "TypeVarInst not expected here"
	go' :: Data a => a -> a
	go' = replaceExpr d r

replaceExpr :: Data a => Expr -> Expr -> a -> a
replaceExpr d r = everywhere (mkT go)
  where go e | e == d    = r 
             | otherwise = e

-- | Is inside the term a definition for the variable?
findReplacer :: TypedExpr -> BoolExpr -> Maybe (BoolExpr -> BoolExpr)
findReplacer tv be = findReplacer' (unTypeExpr tv) be
	
-- | Find a definition, and return a substitution
findReplacer' :: Expr -> BoolExpr -> Maybe (BoolExpr -> BoolExpr)
-- For combined types, look up the components
findReplacer' (Pair x y) e | Just (delX) <- findReplacer' x e
                           , Just (delY) <- findReplacer' y e
                    = Just (delX . delY)
-- Find the definition
findReplacer' e (e1 `Equal` e2) | e == e1    = Just (replaceTermBE e e2)
                                | e == e2    = Just (replaceTermBE e e1)
findReplacer' e (And es)        = listToMaybe (mapMaybe (findReplacer' e) es)
				  -- assuming no two definitions can exist
findReplacer' _ _               = Nothing

-- | Is inside the term a definition for the variable?
defFor :: TypedExpr -> BoolExpr -> Maybe (TypedExpr)
defFor tv be | Just (e') <- defFor' (unTypeExpr tv) be
                         = Just (TypedExpr e' (typeOf tv))
             | otherwise = Nothing
	
-- | Find a definition, and return it along the definition remover
defFor' :: Expr -> BoolExpr -> Maybe (Expr)
defFor' e (e1 `Equal` e2) | e == e1                 = Just (e2)
                          | e == e2                 = Just (e1)
defFor' e (And es)        | [d]  <- mapMaybe (defFor' e) es -- exactly one definition
						    = Just d
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

{- dead code
unCond v (Equal l r) | (Just l') <- isApplOn (unTypeExpr v) l 
	             , (Just r') <- isApplOn (unTypeExpr v) r = 
	if v `occursIn` l' || v `occursIn` r'
	then Condition [v] beTrue (Equal l' r')
	else (Equal l' r')
unCond v e = Condition [v] beTrue e
-}

lambda tv e = TypedExpr inner (Arrow (typeOf tv) (typeOf e))
  where inner | (Just e') <- isApplOn (unTypeExpr tv) (unTypeExpr e)
	      , not (unTypeExpr tv `occursIn` e')
                          = e'
	      | tv == e   = Conc []
              | otherwise = Lambda tv (unTypeExpr e)

conc (Conc xs) (Conc ys) = Conc (xs  ++ ys)
conc (Conc xs)  y        = Conc (xs  ++ [y])
conc x         (Conc ys) = Conc ([x] ++ ys)
conc x          y        = Conc ([x,y])

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
	show (And [])      = "True"
        show (And bes)     = intercalate " && " $ map show bes
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
			(if be1 /= beTrue then indent 2 (show be1) ++ "==>\n" else "") ++
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
