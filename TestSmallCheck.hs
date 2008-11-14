-- |This module uses "Test.Quickcheck" to test the PolyFix package by generating randomly 100 different types
-- running ExFind with that type and then simplifying the generated free theorem
-- to a antilogy of the kind \"() = _|_\" or \"0 = _|_\".
module TestSmallCheck where
import Test.SmallCheck
--import ParseType (parseType')
import SimpleFT  (freeTheorem)
import Expr (specialize,BoolExpr(..),Expr(..))
import ExFindExtended (getCompleteRaw, showTerm, showUsedTermCont,Typ(..),TypVar(..),showTyp,testTerm)
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
import Data.Generics

testrun typ = case getCompleteRaw typ of
              Left _  -> Left "Error in type."
              Right p ->  Right (insertTermsInCondition p (specialize (freeTheorem typ)))

-- *Generation of example types
data VarNum = One | Two | Three | Four | Five | Six deriving(Show)

instance Serial VarNum where
  series = cons0 One 
        \/ cons0 Two  
--        \/ cons0 Three 
        \/ cons0 Four  
        \/ cons0 Five  
--        \/ cons0 Six
data UQuantTyp    = 
              UTVar    VarNum
            | UArrow   UQuantTyp     UQuantTyp
            | UList    UQuantTyp
            --Extensions
            | UInt
            | UTPair    UQuantTyp    UQuantTyp
            | UTEither  UQuantTyp    UQuantTyp
	  deriving(Show)

instance Serial UQuantTyp where
  series = cons1 UTVar
        \/ cons2 UArrow . depth 2
	\/ cons1 UList
	\/ cons0 UInt
	\/ cons2 UTPair . depth 2
--        \/ cons2 UTEither . depth 2   

uQuantTyp2Typ:: UQuantTyp -> Typ
uQuantTyp2Typ utyp = 
  case utyp of
    UTVar x -> TVar (varNum2TypVar x)
    UArrow x y -> Arrow (uQuantTyp2Typ x) (uQuantTyp2Typ y)
    UList x -> List (uQuantTyp2Typ x)
    UInt -> Int
    UTPair x y -> TPair (uQuantTyp2Typ x) (uQuantTyp2Typ y)
    UTEither x y -> TEither (uQuantTyp2Typ x) (uQuantTyp2Typ y)

varNum2TypVar:: VarNum -> TypVar
varNum2TypVar num =
  case num of
    One -> TypVar 1
    Two -> TypVar 2
    Three -> TypVar 3
    Four -> TypVar 4
    Five -> TypVar 5
    Six -> TypVar 6


quantify tau = addquantifiers tau (usedvars tau [])
  where
  usedvars tau vars = case tau of
                        TVar (TypVar i) -> (i:vars)
                        Arrow t1 t2     -> (usedvars t1 []) ++ (usedvars t2 []) ++ vars
                        List t1         -> (usedvars t1 []) ++ vars
			Int             -> vars
			TPair t1 t2     -> (usedvars t1 []) ++ (usedvars t2 []) ++ vars
			TEither t1 t2   -> (usedvars t1 []) ++ (usedvars t2 []) ++ vars
--			_               -> vars
  addquantifiers tau l =  case reverse.sort.nub $ l of
                            []   -> tau
                            x:xs -> if x <= 4 
				    then addquantifiers (AllStar (TypVar x) tau) xs
				    else addquantifiers (All (TypVar x) tau) xs


prop_Classified uqTyp = 
      trace (showTyp typ)(
--    classify (noTerm) "No Term." $
--    classify (equal) "Reduced to Equal" $
--    classify (precond) "Still with Precondition" $
--    classify (true) "True" $
      case testTerm typ of 
        Nothing -> True
        Just _  -> True)
  where typ = quantify (uQuantTyp2Typ uqTyp)
        
