{-# LANGUAGE FlexibleContexts, PatternSignatures, DeriveDataTypeable #-}
module ParseType (
	  parseType
	, parseType'
	, instType
	, unquantify
	, TypVar(..)
	, Typ(..)
	) where

import Language.Haskell.Parser (parseModule, ParseResult(..))
import Language.Haskell.Syntax

import Control.Monad.Error
import Control.Monad.Reader
import Data.List
import qualified Data.Map as M

import Data.Generics
import Data.Generics.Schemes
import Data.Char
import Data.Maybe

data TypVar = TypVar Int        -- alpha, beta etc.
            | TypInst Int Bool  -- t1,t2 etc
	deriving (Show, Eq, Typeable, Data)

instType :: Bool -> Typ -> Typ
instType rightSide typ = everywhere (mkT (\(TypVar i) -> TypInst i rightSide)) typ

data Typ    = TVar    TypVar
            | Arrow   Typ     Typ
            | All     TypVar  Typ       --wir geben Typen ohne Quantifier an
            | AllStar TypVar  Typ
            | List    Typ
            --Extensions
            | Int
            | TPair    Typ     Typ
            | TEither  Typ     Typ
            deriving (Show, Eq, Typeable, Data)

unquantify :: Typ -> Typ
unquantify (All     _ t) = unquantify t
unquantify (AllStar _ t) = unquantify t
unquantify t             = t

parseType :: String -> Typ
parseType = either error id . parseType'

-- | A simple type parser.
--
-- >  parseType "Int -> [Either a b] -> (a,b)" :: Either String Typ
--
--  Right (All (TypVar 3) (All (TypVar 4) (Arrow Int (Arrow (List (TEither (TVar (TypVar 3)) (TVar (TypVar 4)))) (TPair (TVar (TypVar 3)) (TVar (TypVar 4)))))))
--
parseType' :: (MonadError String t) => String -> t Typ
parseType' s =  let (vars,types) = case span (/='.') s of
			(v,'.':t) -> (words v, t)
                        _         -> ([], s)
	 	in case parseModule ("x :: " ++ types) of
		  ParseOk hsModule -> do
			hstype <- extractTheOneType hsModule
			let varmap = createVarMap hstype
			    specials = mapMaybe (flip M.lookup varmap) (map HsIdent vars)
			typ <- runReaderT (simplifiyType hstype) varmap
 			return (quantify specials typ)
		  ParseFailed l _  -> do
			throwError ("Parse error at (" ++ show (srcLine l) ++ ":" ++ show (srcColumn l) ++ ").")

extractTheOneType :: (MonadError String m) => HsModule -> m HsType
extractTheOneType (HsModule _ _ _ _ [HsTypeSig _ _ (HsQualType [] t)]) = return t
extractTheOneType _  = throwError "parseModule gave unexpected result"

createVarMap :: HsType -> M.Map HsName TypVar
createVarMap hstype = M.fromList $ zip
			(nub (listify isVar hstype))
			(map TypVar [1..])
  where isVar (HsIdent (x:_)) | isLower x  = True
        isVar _                            =  False


simplifiyType :: (MonadReader (M.Map HsName TypVar) m, MonadError String m) =>
                 HsType -> m Typ
simplifiyType (HsTyFun t1 t2)
				= liftM2 Arrow (simplifiyType t1) (simplifiyType t2)
simplifiyType (HsTyTuple [t1,t2])
				= liftM2 TPair (simplifiyType t1) (simplifiyType t2)
simplifiyType (HsTyTuple _)	= throwError "Tuple with more than one type not supported."
simplifiyType (HsTyVar name)    = do Just tv <- asks (M.lookup name)
                                     return (TVar tv)
simplifiyType (HsTyCon (UnQual (HsIdent "Int")))
				= return Int
simplifiyType (HsTyApp (HsTyApp (HsTyCon (UnQual (HsIdent "Either"))) t1) t2)
				= liftM2 TEither (simplifiyType t1) (simplifiyType t2)
simplifiyType (HsTyApp (HsTyCon (Special HsListCon)) t)
				= liftM  List (simplifiyType t)
simplifiyType t
				= throwError ("Unsupported type " ++ show t)

quantify :: [TypVar] -> Typ -> Typ
quantify special t = foldr allQuant t (nub (listify (\(_::TypVar) -> True) t))
  where allQuant v | v `elem` special = All v
                   | otherwise        = AllStar v
