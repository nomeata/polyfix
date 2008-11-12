-- |This module uses "Test.Quickcheck" to test the PolyFix package by generating randomly 100 different types
-- running ExFind with that type and then simplifying the generated free theorem
-- to a antilogy of the kind \"_|_ = ()\" or \"_|_ = 0\".
module TestGen where
import Test.QuickCheck
--import ParseType (parseType')
import SimpleFT  (freeTheorem)
import Expr (specialize)
import ExFindExtended (getCompleteRaw, showTerm, showUsedTermCont)
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

import TestItExt

testrun typ = case getCompleteRaw typ of
              Left _  -> Left "Error in type."
              Right p ->  Right (insertTermsInCondition p (specialize (freeTheorem typ)))
