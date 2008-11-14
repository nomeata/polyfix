{-# LANGUAGE PatternGuards, DeriveDataTypeable   #-}
module Expr where

import Data.List
import Data.Maybe
import ParseType

-- import Debug.Trace

import Data.Generics hiding (typeOf)
import Data.Generics.Schemes

data TypedExpr = TypedExpr
	{ unTypeExpr	:: Expr
	, typeOf	:: Typ
	} deriving (Eq, Typeable, Data)

typedLeft, typedRight :: Expr -> Typ -> TypedExpr
typedLeft  e t = TypedExpr e (instType False t)
typedRight e t = TypedExpr e (instType True t)

data EVar = F
	  | FromTypVar Int
          | FromParam Int Bool
            deriving (Eq, Ord, Typeable, Data)

data Expr
	= Var EVar
	| App Expr Expr
	| Conc [Expr] -- Conc [] is Id
	| Lambda Expr Expr
	| Pair Expr Expr
	| Map
	| Const Expr
	| ELeft Expr
	| ERight Expr
	| CaseUnit Expr Expr
	| EitherMap
	| Uncurry
	| HeadMap
	| EUnit
	| Singleton Expr
	| Zero
	| Bottom
            deriving (Eq, Typeable, Data)

data LambdaBE = CurriedEquals Typ
	      | LambdaBE TypedExpr TypedExpr BoolExpr
            deriving (Eq, Typeable, Data)

data BoolExpr 
	= Equal Expr Expr
	| And [BoolExpr] -- And [] is True
	| AllZipWith LambdaBE Expr Expr
	| AndEither  LambdaBE LambdaBE Expr Expr
	| Condition [TypedExpr] BoolExpr BoolExpr
	| UnpackPair TypedExpr TypedExpr TypedExpr BoolExpr
	| TypeVarInst Bool Int BoolExpr
            deriving (Eq, Typeable, Data)

-- Smart constructors

-- | Try eta reduction
equal :: TypedExpr -> TypedExpr -> BoolExpr
equal te1 te2 | typeOf te1 /= typeOf te2 = error "Type mismatch in equal"
              | otherwise                = equal' (unTypeExpr te1) (unTypeExpr te2)

equal' :: Expr -> Expr -> BoolExpr
equal' e1 e2  | (Just (lf,lv)) <- isFunctionApplication e1
              , (Just (rf,rv)) <- isFunctionApplication e2
              , lv == rv 
	      , False
	                                 = equal' lf rf
	      -- This makes it return True...
	      | e1 == e2                 = beTrue
              | otherwise                = Equal e1 e2

-- | If e is of the type (app f1 (app f2 .. (app fn x)..)),
--   return Just (f1 . f2. ... . fn, x)
isFunctionApplication :: Expr -> Maybe (Expr, Expr)
isFunctionApplication (App f e') | (Just (inner,v)) <- isFunctionApplication e'
                                 = Just (conc f inner, v)
                                 | otherwise
                                 = Just (f, e')
isFunctionApplication _          = Nothing


unpackPair :: TypedExpr -> TypedExpr -> TypedExpr -> BoolExpr -> BoolExpr
-- | if the te is already a tuple, then replace the variables
unpackPair v1 v2 te be | Pair pe1 pe2 <- unTypeExpr te
                       = replaceTermBE (unTypeExpr v1) pe1 $
                         replaceTermBE (unTypeExpr v2) pe2 $ be
-- | If both bound variables are just functions, we can replace this
--   by a comparison
unpackPair v1 v2 te be | Just subst1 <- findReplacer v1 be
                       , Just subst2 <- findReplacer v2 be
		       = subst1. subst2 $ (pair v1 v2 `equal` te) `aand` be

-- | Don’t unpack pair if vars are not used
unpackPair v1 v2 te be | not (unTypeExpr v1 `occursIn` be || unTypeExpr v2 `occursIn` be)
                       = be
-- | If the whole tuple is a function, we can replace this
--   by a comparison
unpackPair v1 v2 te be | Just subst <- findReplacer (pair v1 v2) be
		       = subst $ (pair v1 v2 `equal` te) `aand` be
-- | Nothing to optimize
unpackPair v1 v2 te be = UnpackPair v1 v2 te be

pair :: TypedExpr -> TypedExpr -> TypedExpr
pair (TypedExpr e1 t1) (TypedExpr e2 t2) = TypedExpr (Pair e1 e2) (TPair t1 t2)

lambdaBE :: TypedExpr -> TypedExpr -> BoolExpr -> LambdaBE
lambdaBE v1 v2 rel | typeOf v1 == typeOf v2 
                   , rel == v1 `equal` v2    = CurriedEquals (typeOf v1)
	           | otherwise               = LambdaBE v1 v2 rel

andEither :: LambdaBE -> LambdaBE -> TypedExpr -> TypedExpr -> BoolExpr
andEither (CurriedEquals _) (CurriedEquals _) e1 e2 = e1 `equal` e2
andEither lbe1 lbe2 e1 e2 | Just f1 <- arg1IsFunc lbe1
                          , Just f2 <- arg1IsFunc lbe2
			  = e1 `equal` eitherE f1 f2 e2
                          | Just f1 <- arg2IsFunc lbe1
                          , Just f2 <- arg2IsFunc lbe2
			  = eitherE f1 f2 e1 `equal` e2
			  | otherwise
                          = andEither' lbe1 lbe2 (unTypeExpr e1) (unTypeExpr e2)

andEither' :: LambdaBE -> LambdaBE -> Expr -> Expr -> BoolExpr
andEither' (LambdaBE v1 v2 rel) _ (ELeft e1) (ELeft e2)
       = replaceTermBE (unTypeExpr v1) e1 $ replaceTermBE (unTypeExpr v2) e2 $ rel
andEither' _ (LambdaBE v1 v2 rel) (ERight e1) (ERight e2)
       = replaceTermBE (unTypeExpr v1) e1 $ replaceTermBE (unTypeExpr v2) e2 $ rel
andEither' lbe1 lbe2 e1 e2
       = AndEither lbe1 lbe2 e1 e2


arg1IsFunc :: LambdaBE -> Maybe TypedExpr
arg1IsFunc (CurriedEquals t)    = Just $ TypedExpr (Conc []) (Arrow t t)
arg1IsFunc (LambdaBE v1 v2 rel) | Just v1' <- defFor v1 rel
                                = Just (lambda v2 v1')
	                        | otherwise = Nothing

arg2IsFunc :: LambdaBE -> Maybe TypedExpr
arg2IsFunc (CurriedEquals t)    = Just $ TypedExpr (Conc []) (Arrow t t)
arg2IsFunc (LambdaBE v1 v2 rel) | Just v2' <- defFor v2 rel
                                = Just (lambda v1 v2')
	                        | otherwise = Nothing

allZipWith :: TypedExpr -> TypedExpr -> BoolExpr -> TypedExpr -> TypedExpr -> BoolExpr
allZipWith v1 v2 rel e1 e2 | Just v1' <- defFor v1 rel =
				e1 `equal` amap (lambda v2 v1') e2
                           | Just v2' <- defFor v2 rel =
				amap (lambda v1 v2') e1 `equal` e2
                           | otherwise =
				AllZipWith (LambdaBE v1 v2 rel) (unTypeExpr e1) (unTypeExpr e2)

eitherE :: TypedExpr -> TypedExpr -> TypedExpr -> TypedExpr
eitherE f1 f2 e | Arrow lt1 lt2 <- typeOf f1
                , Arrow rt1 rt2 <- typeOf f2
                , TEither lt rt <- typeOf e
                , lt1 == lt
                , rt1 == rt
	= let tEither = TypedExpr EitherMap (Arrow (typeOf f1) (Arrow (typeOf f2) (Arrow (typeOf e) (TEither lt2 rt2))))
          in  app (app (app tEither f1) f2) e
                | otherwise = error $ "Type error in eitherE\n" ++ show (f1, f2, e)

amap :: TypedExpr -> TypedExpr -> TypedExpr
amap tf tl | Arrow t1 t2 <- typeOf tf
           , List t      <- typeOf tl
           , t1 == t
           = let tMap = TypedExpr Map (Arrow (Arrow t1 t2) (Arrow (List t1) (List t2)))
	     in app (app tMap tf) tl
           | otherwise = error "Type error in map"

aand :: BoolExpr -> BoolExpr -> BoolExpr
aand (And xs) (And ys) = And (xs  ++ ys)
aand (And xs) y        = And (xs  ++ [y])
aand x        (And ys) = And ([x] ++ ys)
aand x        y        = And ([x,y])

beTrue :: BoolExpr
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


caseUnit Bottom e = Bottom
caseUnit EUnit e  = e
caseUnit v e      = CaseUnit v e

-- | Replaces a Term in a BoolExpr
replaceTermBE :: Expr -> Expr -> BoolExpr -> BoolExpr
replaceTermBE d r = go
  where go (e1 `Equal` e2) | d == e1 && r == e2 = beTrue
                           | d == e2 && r == e1 = beTrue
                           | otherwise          = go' e1 `equal'` go' e2
        go (And es)        = foldr aand beTrue (map go es)
        go (AllZipWith lbe e1 e2) 
                           = AllZipWith (goL lbe) (go' e1) (go' e2)
        go (AndEither lbe1 lbe2 e1 e2)
			   = andEither' (goL lbe1) (goL lbe2) (go' e1) (go' e2)
	go c@(Condition vs cond concl) -- shadowed definition
			   | d `elem` map unTypeExpr vs 
			   = c
	go (Condition vs cond concl)
			   = condition vs (go cond) (go concl)
	go (UnpackPair v1 v2 e be)
			   = unpackPair v1 v2 (goT e) (go be)
	go (TypeVarInst _ _ _) = error "TypeVarInst not expected here"

	go' = replaceExpr d r

	goT te = te { unTypeExpr = go' (unTypeExpr te) }

	goL (CurriedEquals t)   = (CurriedEquals t)
	goL (LambdaBE v1 v2 be) = lambdaBE v1 v2 (go be)


replaceExpr :: Expr -> Expr -> Expr -> Expr
replaceExpr d r = go
  where go e | e == d    = r
        go (App e1 e2)   = app' (go e1) (go e2)
	go (Conc es)     = foldr conc (Conc []) (map go es)
	go (Lambda v e)  = lambda' v (go e)
	go (Pair e1 e2)  = Pair (go e1) (go e2)
	go (Const e)     = Const (go e)
	go (CaseUnit v e)= caseUnit (go v) (go e)
	go e             = e


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

app :: TypedExpr -> TypedExpr -> TypedExpr
app te1 te2 | Arrow t1 t2 <- typeOf te1
	    , t3          <- typeOf te2 
            , t1 == t3 
            = TypedExpr (app' (unTypeExpr te1) (unTypeExpr te2)) t2
app te1 te2 | otherwise                          = error $ "Type mismatch in app: " ++
                                                           show te1 ++ " " ++ show te2

app' :: Expr -> Expr -> Expr
app' (App HeadMap f) Bottom                 = Bottom
app' (App HeadMap f) (Singleton e)          = app' f e
app' (App Uncurry _) Bottom                 = Bottom
app' (App Uncurry f) (Pair v1 v2)           = f `app'` v1 `app'` v2
app' (App (App EitherMap f1) f2) Bottom     = Bottom
app' (App (App EitherMap f1) f2) (ELeft v)  = ELeft (app' f1 v)
app' (App (App EitherMap f1) f2) (ERight v) = ERight (app' f2 v)
app' Bottom    _   = Bottom    -- _|_ x = _|_
app' (Lambda v e1) (e2) = replaceExpr v e2 e1 -- lambda application
app' (App Map f) (Singleton v) = Singleton (app' f v)
app' Map (Conc []) = Conc []   -- map id = id
app' (Const e) _   = e         -- const x y = x
app' (Conc []) v   = v         -- id x   = x
app' (Conc xs) v   = foldr app' v xs
app' f v           = App f v

lambda :: TypedExpr -> TypedExpr -> TypedExpr
lambda tv e = TypedExpr (lambda' (unTypeExpr tv) (unTypeExpr e))
                        (Arrow (typeOf tv) (typeOf e))

lambda' :: Expr -> Expr -> Expr
lambda' v e  | e == EUnit           = Const EUnit
              | (Just e') <- isApplOn v e
	      , not (v `occursIn` e')
                                     = e'
	      | v == e   = Conc []
              | otherwise            = Lambda v e

conc :: Expr -> Expr -> Expr
conc (Lambda v (CaseUnit v' e)) (Conc ((Const EUnit):r))
				| v == v' = conc (Const e) (Conc r)
conc (Lambda v (CaseUnit v' e)) (Const EUnit) | v == v' = Const e
conc (Conc xs) (Conc ys)        | [x] <- xs ++ ys	= x
                                | otherwise		= Conc (xs  ++ ys)
conc (Conc xs)  y               = Conc (xs  ++ [y])
conc x         (Conc ys)        = Conc ([x] ++ ys)
conc x          y               = Conc ([x,y])


-- Specialization of g'

specialize :: BoolExpr -> BoolExpr
specialize (TypeVarInst strict i be') = 
		replaceTermBE (Var (FromTypVar i)) (if strict then Conc [] else Const EUnit) .
		everywhere (mkT $ go) $
		be
	where be = specialize be'
              go (TypInst i' _) | i' == i = TUnit
              go tv                       = tv                 
-- No need to go further once we are through the quantors
specialize be = be

-- Helpers

isApplOn :: Expr -> Expr -> Maybe Expr
isApplOn e e'         | e == e'                       = Nothing
isApplOn e (App f e') | e == e'                       = Just (Conc [f])
isApplOn e (App f e') | (Just inner) <- isApplOn e e' = Just (conc f inner)
isApplOn _ _                                          = Nothing

occursIn :: (Typeable a, Data a1, Eq a) => a -> a1 -> Bool
e `occursIn` e'       = not (null (listify (==e) e'))

isTuple :: Typ -> Bool
isTuple (TPair _ _) = True
isTuple _           = False


-- showing

-- Precedences:
-- 10 fun app
--  9 (.)
--  8 ==
--  7 ==>
--  6 forall

instance Show EVar where
	show F               = "f"
	show (FromTypVar i)  = "g" ++ show i
	show (FromParam i b) = "x" ++ show i ++ if b then "'" else ""


instance Show Expr where
	showsPrec _ (Var v)     = showsPrec 11 v
	showsPrec d (App e1 e2) = showParen (d>10) $
		showsPrec 10 e1 . showChar ' ' . showsPrec 11 e2
	showsPrec _ (Conc [])   = showString "id"
	showsPrec d (Conc [e])  = showsPrec d e
	showsPrec d (Conc es)   = showParen (d>9) $
		showIntercalate (showString " . ") (map (showsPrec 10) es)
	showsPrec _ (Lambda v e)  = showParen True $ 
				    showString "\\" .
                                    showsPrec 11 v .
                                    showString " -> ".
			            showsPrec 0 e 
	showsPrec _ (Pair e1 e2) = showParen True $ 
			           showsPrec 0 e1 .
				   showString "," .
			           showsPrec 0 e2
	showsPrec _ Zero          = showString "0"
	showsPrec _ EUnit         = showString "()"
	showsPrec _ (Singleton e) = showString "[" . showsPrec 0 e . showString "]"
	showsPrec _ Map           = showString "map"
	showsPrec d (ELeft e)     = showParen (d>10) $ 
					showString "Left ".
					showsPrec 11 e
	showsPrec d (ERight e)    = showParen (d>10) $ 
					showString "Right ".
					showsPrec 11 e
	showsPrec d (Const e)     = showParen (d>10) $ showString "const ".showsPrec 11 e
	showsPrec d (CaseUnit t1 t2) = showParen (d>5) $
					showString "case " .
					showsPrec 0 t1 .
					showString " of () ->  " .
					showsPrec 11 t2
	showsPrec _ EitherMap     = showString "eitherMap"
	showsPrec _ HeadMap       = showString "headMap"
	showsPrec _ Uncurry       = showString "uncurry"
	showsPrec _ Bottom        = showString "_|_"

showIntercalate :: ShowS -> [ShowS] -> ShowS
showIntercalate _ []  = id
showIntercalate _ [x] = x
showIntercalate i (x:xs) = x . i . showIntercalate i xs

instance Show TypedExpr where
	showsPrec d (TypedExpr e t) = 
		showParen (d>10) $
			showsPrec 0 e .
			showString " :: " .
			showString (showTypePrec 0 t)

instance Show LambdaBE where
	show (CurriedEquals _) = 
			"(==)"
	show (LambdaBE v1 v2 be) = 
			"(" ++
			"\\" ++
			showsPrec 11 (unTypeExpr v1) "" ++
			" " ++
			showsPrec 11 (unTypeExpr v2) "" ++
			" -> " ++
			show be ++
			")"

instance Show BoolExpr where
	show (Equal e1 e2) = showsPrec 9 e1 $
			     showString " == " $
			     showsPrec 9 e2 ""
	show (And [])      = "True"
        show (And bes)     = intercalate " && " $ map show bes
	show (AllZipWith lbe e1 e2) =
			"allZipWith " ++
			show lbe ++
			" " ++
			showsPrec 11 e1 "" ++
			" " ++
			showsPrec 11 e2 ""
	show (AndEither lbe1 lbe2 e1 e2) =
			"andEither " ++
			show lbe1 ++
			" " ++
			show lbe2 ++
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
	show (TypeVarInst strict i be) = 
			"forall types t" ++
			show (2*i-1) ++
			", t" ++
			show (2*i) ++
			", " ++
			(if strict then "strict " else "(strict) ") ++
			"functions g" ++
			show i ++
			" :: t" ++
			show (2*i-1) ++
			" -> t" ++
			show (2*i) ++ 
			".\n" ++
			indent 2 (show be)

indent :: Int -> String -> String
indent n = unlines . map (replicate n ' ' ++) . lines

showTypePrec :: Int -> Typ -> String
showTypePrec _ Int			    = "Int" 
showTypePrec _ (TVar (TypVar i))            = "a"++show i
showTypePrec _ (TVar (TypInst i b)) | not b = "t" ++  show (2*i-1)
	      		            |     b = "t" ++  show (2*i)
showTypePrec _ (TVar (TUnit))               = "()"
showTypePrec d (Arrow t1 t2)                = paren (d>9) $ 
						showTypePrec 10 t1 ++
						" -> " ++
						showTypePrec 9 t2 
showTypePrec _ (List t)          	    = "[" ++ showTypePrec 0 t ++ "]"
showTypePrec _ (TEither t1 t2)        	    = "Either " ++ showTypePrec 11 t1 ++ 
					            " " ++ showTypePrec 11 t2
showTypePrec _ (TPair t1 t2)        	    = "(" ++ showTypePrec 0 t1 ++
                                              "," ++ showTypePrec 0 t2 ++ ")"
showTypePrec _ t                            = error $ "Did not expect to show " ++ show t

paren :: Bool -> String -> String
paren b p   =  if b then "(" ++ p ++ ")" else p
