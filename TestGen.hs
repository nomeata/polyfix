-- |This module uses "Test.Quickcheck" to test the PolyFix package by generating randomly 100 different types
-- running ExFind with that type and then simplifying the generated free theorem
-- to a antilogy of the kind \"() = _|_\" or \"0 = _|_\".
module TestGen where
import Test.QuickCheck
--import ParseType (parseType')
import SimpleFT  (freeTheorem)
import Expr (specialize,BoolExpr(..),Expr(..))
import ExFindExtended (getCompleteRaw, showTerm, showUsedTermCont,Typ(..),TypVar(..),showTyp,printTyp,testTerm)

import Foreign
--import Language.Haskell.FreeTheorems.Parser.Haskell98 as FTP
--import Language.Haskell.FreeTheorems
--	( runChecks
--	, check
--	, filterSignatures
--	, prettyTheorem
--	, asTheorem
--	, interpret
--	, unfoldLifts
--	, prettyUnfoldedLift
--	, LanguageSubset(BasicSubset)
--	)
import Term2Expr (term2Expr, termCond2Exprs, insertTermsInCondition)

import List (sort,nub)
import Control.Monad (liftM, liftM2)
import Debug.Trace
import TestItExt

testrun typ = case getCompleteRaw typ of
              Left _  -> Left "Error in type."
              Right p ->  Right (insertTermsInCondition p (specialize (freeTheorem typ)))

-- *Generation of example types

newtype UnpointedVar = UnpointedVar Int
newtype PointedVar = PointedVar Int

-- |restricting the range of unpointed type variables
--instance Arbitrary UnpointedVar where
--  arbitrary = oneof [1,2,3]

-- |restricting the range of pointed type variables
--instance Arbitrary PointedVar where
--  arbitrary = oneof [4,5,6]

-- |TypVar generator
instance Arbitrary TypVar where
--  arbitrary = oneof [UnpointedVar arbitrary, PointedVar arbitrary]
  arbitrary = oneof [return (TypVar 1), return (TypVar 2), return(TypVar 3), return(TypVar 4), return (TypVar 5), return (TypVar 6)]

-- |recursive type generator
instance Arbitrary Typ where
  arbitrary = quantify (sized typ')
    where typ' 0 = frequency [(1, return Int), (6, liftM TVar arbitrary)]
          typ' n | n>0 =
               frequency [(1, liftM TVar arbitrary), (2,liftM2 Arrow subtyp1 subtyp1), (1,liftM List subtyp2), 
		      (1,return Int), (1,liftM2 TPair subtyp1 subtyp1), (1,liftM2 TEither subtyp1 subtyp1)]
	    where subtyp1 = typ' (n `div` 2)
		  subtyp2 = typ' (n-1)
          quantify t = do {tau <- t;
			   return (addquantifiers tau (usedvars tau []))
			  }
	  usedvars tau vars = case tau of
                                TVar (TypVar i) -> (i:vars)
                                Arrow t1 t2     -> (usedvars t1 []) ++ (usedvars t2 []) ++ vars
                                List t1         -> (usedvars t1 []) ++ vars
				Int             -> vars
				TPair t1 t2     -> (usedvars t1 []) ++ (usedvars t2 []) ++ vars
				TEither t1 t2   -> (usedvars t1 []) ++ (usedvars t2 []) ++ vars
--				_               -> vars
	  addquantifiers tau l =  case reverse.sort.nub $ l of
				    []   -> tau
                                    x:xs -> if x < 4 
					    then addquantifiers (AllStar (TypVar x) tau) xs
					    else addquantifiers (All (TypVar x) tau) xs


-- *test properties
-- |returns only True if the free theorem with the example produced leads to the contradiction "() == _|_"
-- or "0 == _|_"
prop_CompletelySolved::Typ -> Bool
prop_CompletelySolved typ = 
    case getCompleteRaw typ of
      Left _  -> False
      Right p -> case (insertTermsInCondition p (specialize (freeTheorem typ))) of
		   Equal Zero Bottom  -> True
		   Equal EUnit Bottom -> True
		   _                  -> False


-- |returns only True if the free theorem with the example produced leads to the an expression of the form "expr1 == expr2"
prop_DownToEqual typ =
    case getCompleteRaw typ of
      Left _  -> False
      Right p -> case (insertTermsInCondition p (specialize (freeTheorem typ))) of
		   Equal _ _  -> True
		   _          -> False

prop_Test typ = trace (showTyp typ) True

--prop_Classified :: Typ -> IO Property
prop_Classified typ = 
--    do {print typ;
--error (showTyp typ)
--	return (
        trace (showTyp typ)
	(classify (noTerm) "No Term." $
	classify (equal) "Reduced to Equal" $
	classify (precond) "Still with Precondition" $
	classify (true) "True" $
	True)
--       }
  where noTerm = case testTerm typ of
                   Nothing -> True
		   _       -> False
	equal = if not noTerm 
		then
                  case getCompleteRaw typ of
                    Left _  -> False
                    Right p -> case (insertTermsInCondition p (specialize (freeTheorem typ))) of
		                 Equal _ _  -> True
		                 _          -> False
		else False
	precond = if not noTerm 
		  then
		    case getCompleteRaw typ of
		      Left _  -> False
                      Right p -> case (insertTermsInCondition p (specialize (freeTheorem typ))) of
		                   Equal _ _  -> False
		                   And []     -> False
		                   _          -> True
		  else False
	true    = if not noTerm 
		  then
		    case getCompleteRaw typ of
		      Left _  -> False
                      Right p -> case (insertTermsInCondition p (specialize (freeTheorem typ))) of		                
				   And []     -> True
		                   _          -> False
		  else False

check_Classified typ test = case test of
			     1 -> noTerm
			     2 -> equal
			     3 -> precond
			     4 -> true
  where noTerm = case testTerm typ of
                   Nothing -> True
		   _       -> False
	equal = if not noTerm 
		then
                  case getCompleteRaw typ of
                    Left _  -> False
                    Right p -> case (insertTermsInCondition p (specialize (freeTheorem typ))) of
		                 Equal _ _  -> True
		                 _          -> False
		else False
	precond = if not noTerm 
		  then
		    case getCompleteRaw typ of
		      Left _  -> False
                      Right p -> case (insertTermsInCondition p (specialize (freeTheorem typ))) of
		                   Equal _ _  -> False
		                   And []     -> False
		                   _          -> True
		  else False
	true    = if not noTerm 
		  then
		    case getCompleteRaw typ of
		      Left _  -> False
                      Right p -> case (insertTermsInCondition p (specialize (freeTheorem typ))) of		                
				   And []     -> True
		                   _          -> False
		  else False

prop_HowManyTerms typ =
    classify (findsTerm)  "Term" $
    classify (not findsTerm) "No Term" $
    True
  where findsTerm = if (testTerm typ) == Nothing then False else True

mainTest = quickCheck prop_Classified
