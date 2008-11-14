{-# LANGUAGE PatternGuards #-}

module Term2Expr (insertTermsInCondition, term2Expr, termCond2Exprs) where

import ExFindExtended
import Expr
import qualified ExFindExtended as T
import qualified Expr as E
import Debug.Trace
import qualified Data.Map as M
import Data.Generics
import Data.List

insertTermsInCondition :: (T.Term,T.TermCont) -> BoolExpr -> BoolExpr
insertTermsInCondition (t,tc) =
	replaceTermBE (E.Var F) f .
	replaceBinds binds 
  where f = term2Expr t
	binds = termCond2Exprs tc


replaceBinds :: M.Map EVar Expr -> BoolExpr -> BoolExpr
replaceBinds binds = gmapT (mkT (replaceBinds binds)) `extT` go
  where go (Condition vars cond concl)
		= let (toReplace, notToReplace) = partition isReplaced vars
                      subst be = M.foldWithKey replaceBind be binds
		      binds' = M.filterWithKey (\v _ -> any ((==Just v).getVar) vars) binds
		  in  condition notToReplace
				(replaceBinds binds' (subst cond))
			        (replaceBinds binds' (subst concl))
        go be = gmapT (mkT (replaceBinds binds)) be
				
	replaceBind v t = replaceTermBE (E.Var v) t

        isReplaced te | Just v <- getVar te = v `M.member` binds
        isReplaced _                     = False

        getVar (TypedExpr (E.Var v) _) = Just v
	getVar _                       = Nothing


term2Expr :: T.Term -> E.Expr
term2Expr = absTerm2Expr (const E.EUnit)

termPlus2Expr :: T.TermPlus -> E.Expr
termPlus2Expr = absTerm2Expr (\(PlusElem _ i) -> EUnit)


termCond2Exprs = M.fromList . concatMap
		 (\(TermVar i,(tp1,tp2)) -> [
			(FromParam i False, termPlus2Expr tp1) ,
		        (FromParam i True,  termPlus2Expr tp2) ] )
		. M.assocs

absTerm2Expr :: (Eq a) => (a -> Expr) -> AbsTerm a -> Expr
absTerm2Expr ex (T.Var v)       = E.Var (termVar2EVar v)
absTerm2Expr ex (T.Abs v vt at) = lambda' (E.Var (termVar2EVar v)) (absTerm2Expr ex at)
absTerm2Expr ex (T.App t1 t2)   = E.App (absTerm2Expr ex t1) (absTerm2Expr ex t2)
absTerm2Expr ex (T.TAbs _ at)   = absTerm2Expr ex at
absTerm2Expr ex (Nil _)         = trace "Can not convert Nil" undefined
absTerm2Expr ex (Cons e (Nil _))= Singleton (absTerm2Expr ex e)
absTerm2Expr ex (Cons _ _)      = trace "Can not convert non-singleton Cons" undefined
absTerm2Expr ex (Case e _ v b)  = app' (app' HeadMap
                                             (lambda' (E.Var (termVar2EVar v))
                                                      (absTerm2Expr ex b)))
                                             (absTerm2Expr ex e)
absTerm2Expr ex (T.Bottom t)    = E.Bottom
absTerm2Expr ex (Extra e)       = ex e

absTerm2Expr ex (Case1 t _ z w) | z == w = E.CaseUnit (absTerm2Expr ex t) (absTerm2Expr ex w)
absTerm2Expr ex (Case1 _ _ _ _) = trace "Can not convert Case1" undefined
absTerm2Expr ex T.Zero          = E.Zero
absTerm2Expr ex (T.Pair t1 t2)  = E.Pair (absTerm2Expr ex t1) (absTerm2Expr ex t2)
absTerm2Expr ex (T.ECase e vl el vr er)
				= app' ( app' (app' EitherMap
				   (lambda' (E.Var (termVar2EVar vl)) (absTerm2Expr ex el)) )
				   (lambda' (E.Var (termVar2EVar vr)) (absTerm2Expr ex el)) )
                                   (absTerm2Expr ex e)
absTerm2Expr ex (T.Right t)     = ERight (absTerm2Expr ex t)
absTerm2Expr ex (T.Left  t)     = ELeft (absTerm2Expr ex t)
absTerm2Expr ex (T.PCase pt v1 v2 e) = Uncurry `app'`
				(lambda' (E.Var (termVar2EVar v1))
                                         (lambda' (E.Var (termVar2EVar v2))
                                                  (absTerm2Expr ex e)))
                                `app'` (absTerm2Expr ex pt)

termVar2EVar (T.TermVar i) = E.FromTypVar i


