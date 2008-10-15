module ExFindExtended (TypVar(..),Typ(..),TermVar(..),Term,AbsTerm(..),testTerm,getTerm,getComplete,getWithDebug,getIt) where

import Prelude hiding (Either(..))
import List
import qualified Data.Map as Map
import Control.Monad
import M
import ParseType
--import Debug.Trace
trace string a = a
-- newInt :: M Int
-- runM :: M a -> a

type TypedVar = (TermVar,Typ)
type TermCont = Map.Map TermVar (TermPlus,TermPlus)

--newtype TypVar = TypVar Int deriving (Show, Eq)

--data Typ    = TVar    TypVar
--	    | Arrow   Typ     Typ
--	    | All     TypVar  Typ       --wir geben Typen ohne Quantifier an
--	    | AllStar TypVar  Typ
--	    | List    Typ
--	    deriving (Show, Eq)

newtype TermVar = TermVar Int deriving (Show, Eq, Ord)

data PlusElem = PlusElem TypVar Int

type Term = AbsTerm ()
type TermPlus = AbsTerm PlusElem
data AbsTerm a  = Var TermVar   
	    | Abs     TermVar     Typ         (AbsTerm a)
	    | App     (AbsTerm a) (AbsTerm a)
	    | TAbs    TypVar      (AbsTerm a)
--	    | TApp    Term    Typ       -- nie benutzt
	    | Nil     Typ
	    | Cons    (AbsTerm a) (AbsTerm a) 
	    | Case    (AbsTerm a) (AbsTerm a) TermVar     (AbsTerm a)
	    | Bottom  Typ               -- statt Fix
--	    | GoalTerm Cont Typ         -- nur temporaer
--	    | Subst    Term Term TermVar-- nur temporaer
--	    | Alg2     Cont Typ --nur temporaer
--          Erweiterung fuer die Beispielkonstruktion
            | Extra    a 
	    -- case    x       of {y        ->  z;     _ -> w}
	    | Case1    (AbsTerm a) (AbsTerm a)  (AbsTerm a) (AbsTerm a)
------------Erweiterung fuer Extended Algorithmus
	    | Zero
	    | Pair     (AbsTerm a) (AbsTerm a)
	    | PCase    (AbsTerm a) TermVar      TermVar     (AbsTerm a)
	    | ECase    (AbsTerm a) TermVar      (AbsTerm a) TermVar     (AbsTerm a)
	    | Right    (AbsTerm a)
	    | Left     (AbsTerm a)
	    deriving (Show, Eq)


data Cont   = Cont { tVars :: [TypVar], tVarsStar :: [TypVar], vars :: [(TermVar,Typ)], varsStar :: [(TermVar,Typ)] } deriving (Show,Eq) --TODO: Eq wieder loeschen

emptyCont :: Cont
emptyCont = Cont [] [] [] []

emptyTermCont :: TermCont
emptyTermCont = Map.empty

updateTVarStar (Cont tVars tVarsStar vars varsStar) tv = Cont tVars (tv:tVarsStar) vars varsStar

updateTVar (Cont tVars tVarsStar vars varsStar) tv = Cont (tv:tVars) tVarsStar vars varsStar

updateVar (Cont tVars tVarsStar vars varsStar) v tau = Cont tVars tVarsStar ((v,tau):vars) varsStar
removeVar (Cont tVars tVarsStar vars varsStar) var = Cont tVars tVarsStar (filter ((/= var).fst) vars) varsStar

updateVarStar (Cont tVars tVarsStar vars varsStar) v tau = Cont tVars tVarsStar vars  ((v,tau):varsStar)
removeVarStar (Cont tVars tVarsStar vars varsStar) var = Cont tVars tVarsStar vars  (filter ((/= var).fst) varsStar)

unpointed tvars tau = case tau of
                      TVar tvar      -> case find (== tvar) tvars of
                                          Nothing -> False
                                          _       -> True
                      Arrow _ tau'   -> unpointed tvars tau'
                      All tvar tau'  -> unpointed (tvar:tvars) tau'
                      AllStar _ tau' -> unpointed tvars tau'
                      List _         -> False
		      Int            -> False
                      TPair _ _      -> False
                      TEither _ _    -> False

findfirstSpecialType vars typ =
    case vars of
      []     -> Nothing
      (x:xs) -> if snd x == typ
		then Just x
		else findfirstSpecialType xs typ

findfirstWithTVars typecheckfunction tvars vars =
    case vars of
      []     -> Nothing
      (x:xs) -> if typecheckfunction tvars (snd x)
		then Just x 
		else findfirstWithTVars typecheckfunction tvars xs

findallWithTVars typecheckfunction tvars vars = 
    case vars of
      []     -> []
      (x:xs) -> if typecheckfunction tvars (snd x)
		then (x:(findallWithTVars typecheckfunction tvars xs))
		else findallWithTVars typecheckfunction tvars xs

findfirst typecheckfunction vars = case vars of
                                     []     -> Nothing
                                     (x:xs) -> if typecheckfunction (snd x) 
               				       then Just x 
				               else findfirst typecheckfunction xs

findall typecheckfunction vars = case vars of
                                   []     -> []
                                   (x:xs) -> if typecheckfunction (snd x)
					     then (x:(findall typecheckfunction xs))
			                     else findall typecheckfunction xs

-- fuer (lIArrow)
typeCheckArrowListArg tau = case tau of
                              Arrow tau1 _ -> case tau1 of
                                                List _ -> True
                                                _      -> False
			      _            -> False

typeCheckList tau = case tau of
                     List _ -> True
                     _      -> False

typeCheckArrowUnPointedArg tvars tau = case tau of
                                      Arrow tau1 _ -> unpointed tvars tau1
                                      _            -> False

typeCheckArrowArgArrow tau = case tau of
			      Arrow tau1 _ -> case tau1 of
						Arrow _ _ -> True
						_         -> False
			      _            -> False

typeCheckArrow tau = case tau of
		       Arrow _ _ -> True
		       _         -> False

typeCheckInt tau = case tau of
		     Int -> True
		     _   -> False

typeCheckPair tau = case tau of
		      TPair _ _ -> True
		      _         -> False

typeCheckArrowPairArg tau = case tau of
			      Arrow tau1 _ -> case tau1 of
					        TPair _ _ -> True
						_         -> False
			      _            -> False

typeCheckArrowEitherArg tau = case tau of
			        Arrow tau1 _ -> case tau1 of
						  TEither _ _ -> True
						  _           -> False
				_            -> False

typeCheckEither tau = case tau of
		        TEither _ _ -> True
			_           -> False

apply :: AbsTerm a -> [AbsTerm a] -> AbsTerm a
apply f args = case args of
	        []    -> f
	        x:xs  -> apply (App f x) xs

subst :: Term -> Term -> TermVar -> Term
subst m new old = case m of
		   Var var           -> if(var == old) then new else m
		   Abs v tau m'      -> Abs v tau (subst m' new old)
                   App m1 m2         -> App (subst m1 new old) (subst m2 new old)
                   TAbs tau m'       -> TAbs tau (subst m' new old)
                   Cons m1 m2        -> Cons (subst m1 new old) (subst m2 new old)
                   Case m0 m1 v2 m2  -> Case (subst m0 new old) (subst m1 new old) v2 (subst m2 new old)
		   Pair m1 m2        -> Pair (subst m1 new old) (subst m2 new old)
		   PCase m0 v1 v2 m1 -> PCase (subst m0 new old) v1 v2 (subst m1 new old)
		   Right m           -> Right (subst m new old)
                   Left m            -> Left (subst m new old)
                   ECase m0 v1 m1 v2 m2 -> ECase (subst m0 new old) v1 (subst m1 new old) v2 (subst m2 new old)
--                 GoalTerm _ _  -> Subst m new old
--		   Subst _ _ _   -> Subst m new old
--		   Alg2 _ _       -> Subst m new old
                   _                 -> m

makePlusPair :: Typ -> Maybe (AbsTerm PlusElem, AbsTerm PlusElem)
makePlusPair tau = let x = makePlusElem tau in 
			   case x of 
			     Just t -> Just (t,t)
			     _      -> Nothing

makePlusElem :: Typ -> Maybe (AbsTerm (PlusElem))
makePlusElem tau = case tau of
		   TVar  var         -> Just (Extra (PlusElem var 0))
		   Arrow tau1 tau2   -> let x = makePlusElem tau2 in
					      case x of 
						     Just t -> Just (Abs (TermVar 0) tau1 t)
						     _      -> Nothing
                   List  tau         -> let x = makePlusElem tau in
					      case x of 
						     Just t -> Just (Cons t (Nil tau))
						     _      -> Nothing
		   Int               -> Just Zero
                   TPair tau1 tau2   -> let x = makePlusElem tau1 in
						case x of
						       Just t1 -> let y = makePlusElem tau2 in
								          case y of
									    Just t2 -> Just (Pair t1 t2)
									    Nothing -> Nothing
                                                       Nothing -> Nothing
                   
                   TEither tau1 tau2 -> let x = makePlusElem tau1 in
					case x of 
					  Just t1 -> Just (Left t1)
					  _       -> let x = makePlusElem tau2 in
						     case x of
						       Just t2 -> Just (Right t2)
						       _       -> Nothing
		   _                 -> Nothing

-------Regeln der ersten Phase-------------

rFix :: Cont -> Typ -> Maybe Term
rFix gamma tau = if unpointed (tVars gamma) tau
		 then Just (Bottom tau)
		 else Nothing

rAllStar :: Cont -> Typ -> Maybe (Cont, Typ, Term -> Term)
rAllStar gamma tau = case tau of
		       AllStar tv tau' -> Just (updateTVarStar gamma tv, tau', \m -> TAbs tv m)
		       _               -> Nothing

rAll :: Cont -> Typ -> Maybe (Cont, Typ, Term -> Term)
rAll gamma tau = case tau of
		   All tv tau' -> Just (updateTVar gamma tv, tau', \m -> TAbs tv m)
		   _           -> Nothing

rArrow :: Cont -> Typ -> Maybe (M (Cont, Term -> Term), Typ)
rArrow gamma tau = case tau of
		   Arrow tau1 tau2 -> Just (do {i <- newInt; 
						let x = TermVar i in
						return (updateVar gamma x tau1, \m -> Abs x tau1 m)		       
					       }
					   , tau2)
		   _               -> Nothing

rI :: Typ -> Maybe (Typ, Term -> Term)
rI tau = case tau of
               List tau' -> Just (tau', \m -> Cons m (Nil tau'))
               _         -> Nothing

lIArrow :: Cont -> Maybe (M ((Cont, Term -> Term),(TypedVar, TypedVar)))
lIArrow gamma = let f = findfirst typeCheckArrowListArg (vars gamma) in
                    case f of
                      Nothing ->      Nothing
		      Just (v, (Arrow (List tau1) tau2)) -> 
                           Just (do {i <- newAux; --g fuer den neuen Kontext
			             j <- newInt; --y fuer die Ersetzung
			            let g = TermVar i
				        y = TermVar j in				   
				    return ((updateVar (removeVar gamma v) g (Arrow tau1 tau2),
					    \m -> subst m (Abs y tau1 (App (Var v) (Cons (Var y) (Nil tau1)))) g),
					    ((g,Arrow tau1 tau2), (v, Arrow (List tau1) tau2)))
				    })

lIArrow_tc_update :: TermCont -> TermVar -> TermVar -> TypedVar -> TypedVar -> TermCont
lIArrow_tc_update tc l h g f = let Arrow (List t1) t2 = snd f
			           Just (x,y) = if Map.member (fst g) tc 
						then Just ((fst (trace "Map.!-check: lIArrow fst g" (tc Map.! (fst g)))),(snd (trace "Map.!-check: lIArrow snd g" (tc Map.! (fst g)))))
					        else trace "lIArrow not used" $ makePlusPair (snd g) 
			       in
			       Map.insert (fst f) (Abs l  (List t1) (Case (Var l) (Bottom t2) h (App x (Var h))),Abs l (List t1) (Case (Var l) (Bottom t2) h (App y (Var h)))) tc

lI :: Cont -> Typ -> Maybe (M ((Cont, Term -> Term),(TypedVar,TypedVar)))
lI gamma tau' = let l = findfirst typeCheckList (vars gamma) in
		case l of
                  Nothing           -> Nothing
                  Just (v,List tau) -> Just (do {i <- newInt; --h
						 let h = TermVar i in
						 return ((updateVar (removeVar gamma v) h tau,
							  \m -> subst m (Case (Var v) (Bottom tau) h (Var h)) h),
							 ((h,tau),(v,List tau)))
						})

lI_tc_update :: TermCont -> TypedVar -> TypedVar -> TermCont
lI_tc_update tc h l = let Just (x,y) = if Map.member (fst h) tc 
				       then Just ((fst (trace "Map.!-check: lI fst h" (tc Map.! (fst h)))),(snd (trace "Map.!-check: lI snd h" (tc Map.! (fst h)))))
				       else trace "lI not used" $ makePlusPair (snd h) 
		      in
		      Map.insert (fst l) (Cons x (Nil (snd h)), Cons y (Nil (snd h))) tc

lInt :: Cont -> Maybe Cont
lInt gamma = let l = findfirst typeCheckInt (vars gamma) in
	       case l of
		 Nothing  -> Nothing
                 Just var -> Just (removeVar gamma (fst var))

lFix :: Cont -> Maybe Cont
lFix gamma = let l = findfirstWithTVars unpointed (tVars gamma) (vars gamma) in
                 case l of
		   Nothing    -> Nothing
		   Just var   -> Just (removeVar gamma (fst var))

--TODO START--
lPArrow :: Cont -> Maybe (M ((Cont, Term -> Term),(TypedVar,TypedVar)))
lPArrow gamma = let l = findfirst typeCheckArrowPairArg (vars gamma) in
		    case l of
		      Nothing  -> Nothing
		      Just (f, (Arrow (TPair tau1 tau2) tau3)) -> 
			   Just (do {i <- newAux; --g fuer den neuen Kontext
				     j <- newInt;
				     k <- newInt;
				     let g = TermVar i 
				         x = TermVar j
				         y = TermVar k in
				     return ((updateVar (removeVar gamma f) g (Arrow tau1 (Arrow tau2 tau3)),
					     \m -> subst m (Abs x  tau1 (Abs y tau2 (App (Var f) (Pair (Var x) (Var y))))) g),((g,Arrow tau1 (Arrow tau2 tau3)),(f,(Arrow (TPair tau1 tau2) tau3))))
				    })

lPArrow_tc_update :: TermCont -> TypedVar -> TypedVar -> M (TermCont)
lPArrow_tc_update tc g f = do {i <- newInt;
			       j <- newInt;
			       k <- newInt;
			       let p = TermVar i
			           x = TermVar j
				   y = TermVar k 
			           Arrow tau tau3 = snd f 
			           Just (z,z') = if Map.member (fst g) tc then Just (fst (trace "Map.!-check: lPArrow fst g" (tc Map.! (fst g))), snd (trace "Map.!-check: lPArrow snd g" (tc Map.! (fst g))))
			                         else makePlusPair $ snd g 
			       in
			       return (Map.insert (fst f) (Abs p tau (PCase (Var p) x y (App (App z (Var x)) (Var y))),Abs p tau (PCase (Var p) x y (App (App z' (Var x)) (Var y)))) tc)
			      }

lP :: Cont -> Maybe (M ((Cont, Term -> Term),([TypedVar],TypedVar)))
lP gamma = let l = findfirst typeCheckPair (vars gamma) in
	       case l of
		 Nothing -> Nothing
		 Just (p, TPair tau1 tau2) ->
		      Just (do {i <- newInt;
				j <- newInt;
				k <- newInt;
				l <- newInt;
				let x = TermVar i
				    y = TermVar j 
				    u = TermVar k
				    v = TermVar l in
				return ((updateVar (updateVar (removeVar gamma p) x tau1) y tau2,
				         \m -> subst (subst m (PCase (Var p) u v (Var u)) x) (PCase (Var p) u v (Var v)) y),
					 ([(x,tau1),(y,tau2)],(p,TPair tau1 tau2)))
			       })

lP_tc_update :: TermCont -> [TypedVar] -> TypedVar -> TermCont
lP_tc_update tc varIn p = let [x,y] = varIn 
			      Just (z,z') = if Map.member (fst x) tc then Just (fst (trace "Map.!-check: lP fst x" (tc Map.! (fst x))), snd (trace "Map.!-check: lP snd x" (tc Map.! (fst x))))
					    else makePlusPair $ snd x 
			      Just (u,u') = if Map.member (fst y) tc then Just (fst (trace "Map.!-check: lP fst y" (tc Map.! (fst y))), snd (trace "Map.!-check: lP snd y" (tc Map.! (fst y))))
					    else makePlusPair $ snd y
			  in
			  Map.insert (fst p) (Pair z u, Pair z' u') tc


lEArrow :: Cont -> Maybe (M ((Cont, Term -> Term),([TypedVar],TypedVar)))
lEArrow gamma = let l = findfirst typeCheckArrowEitherArg (vars gamma) in
	            case l of
		      Nothing -> Nothing
		      Just (f, (Arrow (TEither tau1 tau2) tau3)) ->
			   Just (do {i <- newAux; --g im neuen Kontext
				     j <- newAux; --h im neuen Kontext
				     k <- newInt; --x im Term
				     l <- newInt; --y im Term
				     let g = TermVar i
				         h = TermVar j
				         x = TermVar k
				         y = TermVar l in
				     return ((updateVar (updateVar (removeVar gamma f) g (Arrow tau1 tau3)) h (Arrow tau2 tau3),
					     \m -> subst (subst m (Abs x tau1 (App (Var f) (Left (Var x)))) g) (Abs y tau2 (App (Var f) (Right (Var y)))) h),
					     ([(g,Arrow tau1 tau3),(h,Arrow tau2 tau3)],(f,(Arrow (TEither tau1 tau2) tau3))))
				    })

lEArrow_tc_update :: TermCont -> [TypedVar] -> TypedVar -> M (TermCont)
lEArrow_tc_update tc varIn f = let [g,h] = varIn in
                               do{i <- newInt;
				  j <- newInt;
				  k <- newInt;
				  let e = TermVar i 
				      x = TermVar j
				      y = TermVar k 
				      Arrow tau tau3 = snd f 
			              Just (z,z') = if Map.member (fst g) tc then Just (fst (trace "Map.!-check: lEArrow fst g" (tc Map.! (fst g))), snd (trace "Map.!-check: lEArrow snd g" (tc Map.! (fst g))))
				                    else makePlusPair $ snd g
				      Just (u,u') = if Map.member (fst h) tc then Just (fst (trace "Map.!-check: lEArrow fst h" (tc Map.! (fst h))), snd (trace "Map.!-check: lEArrow snd h" (tc Map.! (fst h))))
				                    else makePlusPair $ snd h
				  in
	  			  return (Map.insert (fst f) (Abs e tau (ECase (Var e) x z y u), Abs e tau (ECase (Var e) x z' y u')) tc)
				 }

------Regeln mit backtracking -----------------

lE1 :: Cont -> Typ -> Maybe (M ((Cont, Term -> Term),(TypedVar,TypedVar)))
lE1 gamma tau = case findfirst typeCheckEither (vars gamma) of
                    Nothing -> Nothing
                    Just (e, TEither tau1 tau2) ->
		         Just (do {i <- newInt;
			   	   j <- newInt;
				   let x = TermVar i
			               y = TermVar j in
				   return ((updateVar (removeVar gamma e) x tau1,
					   \m -> subst m (ECase (Var e) x (Var x) y (Bottom tau1)) x),
					   ((x,tau1),(e, TEither tau1 tau2)))
				  })

lE1_tc_update :: TermCont -> TypedVar -> TypedVar -> TermCont
lE1_tc_update tc x e = let Just (z,z') = if Map.member (fst x) tc then Just (fst (trace "Map.!-check: lE1 fst x" (tc Map.! (fst x))), snd (trace "Map.!-check: lE1 snd x" (tc Map.! (fst x))))
					 else makePlusPair $ snd x
		       in
		       Map.insert (fst e) (Left z, Left z') tc

lE2 :: Cont -> Typ -> Maybe (M ((Cont, Term -> Term),(TypedVar,TypedVar)))
lE2 gamma tau = case findfirst typeCheckEither (vars gamma) of
                    Nothing -> Nothing
                    Just (e, TEither tau1 tau2) ->
		         Just (do {i <- newInt;
			   	   j <- newInt;
				   let x = TermVar i
			               y = TermVar j in
				   return ((updateVar (removeVar gamma e) y tau2,
					   \m -> subst m (ECase (Var e) x (Bottom tau2) y (Var y)) y),
					   ((y,tau2),(e,TEither tau1 tau2)))
				  })
lE2_tc_update :: TermCont -> TypedVar -> TypedVar -> TermCont
lE2_tc_update tc y e = let Just (z,z') = if Map.member (fst y) tc then Just (fst (trace "Map.!-check: lE2 fst y" (tc Map.! (fst y))), snd (trace "Map.!-check: lE2 snd y" (tc Map.! (fst y))))
					 else makePlusPair $ snd y
		       in
		       Map.insert (fst e) (Right z, Right z') tc

rP1 :: Typ -> Maybe (Typ, Term -> Term)
rP1 tau = case tau of
            TPair tau1 tau2 -> Just (tau1, \m -> Pair m (Bottom tau2))
	    _               -> Nothing

rP2 :: Typ -> Maybe (Typ, Term -> Term)
rP2 tau = case tau of
            TPair tau1 tau2 -> Just (tau2,\m -> Pair (Bottom tau1) m)
	    _               -> Nothing

rE1 :: Typ -> Maybe (Typ, Term -> Term)
rE1 tau = case tau of
	    TEither tau1 _ -> Just(tau1, \m -> Left m)
            _              -> Nothing

rE2 :: Typ -> Maybe (Typ, Term -> Term)
rE2 tau = case tau of
	    TEither _ tau2 -> Just(tau2, \m -> Right m)
            _              -> Nothing
---TODO END---

lFixArrowStar :: Cont -> [M ((Cont, Term -> Term),(TypedVar,TypedVar))]
lFixArrowStar gamma = let l = findallWithTVars typeCheckArrowUnPointedArg (tVars gamma) (vars gamma) in
                          map makeone l
		          where makeone = \var -> let Arrow tau1 tau2 = snd var in
					               do {i <- newAux;
							    let x = TermVar i in
							    return (((updateVarStar (removeVar gamma (fst var)) x tau2)
							             , \m -> subst m (App (Var (fst var)) (Bottom tau1)) x),((x,tau2),var))
							  }
lFixArrowStar_tc_update :: TermCont -> TermVar -> TypedVar -> TypedVar -> TermCont
lFixArrowStar_tc_update tc x y f = let Arrow t1 t2 = snd f
				       ana = lFixArrowStar_typeAnalyse t1 ([],[]) 
				       (u,u') = if Map.member (fst y) tc 
						then trace "LFIXARROWSTAR: y in Map" (tc Map.! (fst y)) 
						else trace "LFIXARROWSTAR: y NOT in Map"
						     (case makePlusPair (snd y) of 
						     Just p -> p) 
				   in
				   case makePlusPair (snd ana) of
				   Just (z,_) -> Map.insert (fst f) (Abs x t1 u, Abs x t1 (Case1 (apply (Var x) (fst (fst ana))) z u' u')) tc

lFixArrowStar_typeAnalyse :: Typ -> ([TermPlus],[TermPlus]) -> (([TermPlus],[TermPlus]),Typ)
lFixArrowStar_typeAnalyse tau args = case tau of
				     TVar t      -> (args,tau)
				     Arrow t1 t2 -> case makePlusPair t1 of
                                                    Just (x,y) -> lFixArrowStar_typeAnalyse t2 (x:(fst args), y:(snd args))
--lArrowArrow in der Variante ohne g.
lArrowArrow :: Cont -> [M (((Cont, Typ), Cont, Term -> Term -> Term), ([TypedVar],TypedVar))]
lArrowArrow gamma = 
    let l = findall typeCheckArrowArgArrow (vars gamma) in
    map makeone l
    where makeone var = let Arrow (Arrow tau1 tau2) tau3 = snd var in
	                do {i <- newInt;
			    j <- newInt;
			    let x = TermVar i 
			        y = TermVar j in
			    return ((((updateVar (removeVar gamma (fst var)) x tau1),
				     tau2),
				     updateVarStar (removeVar gamma (fst var)) y tau3,
				     \m1 -> \m2 -> subst m2 (App (Var (fst var)) (Abs x tau1 m1)) y),
				    ([(x,tau1),(y,tau3)],var))
			   }
------------------------ TermContext         M_1     w           y           f           TermContext -----
lArrowArrow_tc_update :: TermCont -> Cont -> Term -> TypedVar -> TypedVar -> TypedVar -> M TermCont
lArrowArrow_tc_update tc gamma m1 w y f = 
    let Arrow t12 t3 = snd f 
	Arrow t1  t2 = t12 in
    do {i <- newInt;
	(g,g') <- (lArrowArrow_construct_g tc gamma t2 t2 ([],[]) m1 y);
	let u = TermVar i 
	    Just (z,z') = if Map.member (fst w) tc then Just (fst (trace "Map.!-check: lArrowArrow fst w" (tc Map.! (fst w))), snd (trace "Map.!-check: lArrowArrow snd w" (tc Map.! (fst w))))
	                  else makePlusPair $ snd w
	in
        return (Map.insert (fst f) (Abs u t12 (App g (App (Var u) z)), Abs u t12 (App g' (App (Var u) z'))) tc)
       }

lArrowArrow_construct_g :: TermCont -> Cont -> Typ -> Typ -> ([TermPlus],[TermPlus]) -> Term -> TypedVar -> M (TermPlus,TermPlus)
lArrowArrow_construct_g tc gamma tau tau1 args m1 y = 
    let Just (z,z') = if Map.member (fst y) tc then Just (fst (trace "Map.!-check: lArrowArrow g-construct fst y (else)" (tc Map.! (fst y))), snd (trace "Map.!-check: lArrowArrow g-construct snd y" (tc Map.! (fst y))))
		      else trace "lArrowArrow not used" $ makePlusPair (snd y)
    in
    case tau1 of
      TVar beta    -> case makePlusPair tau1 of
		       Just (u,v) -> do {i <- newInt;
					 let w  = TermVar i
					     g' = Abs w tau (Case1 (apply (Var w) (snd args)) v z' z') in
					 if unpointed (tVars gamma) tau
					 then return (Abs w tau z, g')
					 else return (Abs w tau (Case1 (apply (Var w) (fst args)) u z z), g')
					}
      List tau'    -> case m1 of
		        Bottom _ -> do{i <- newInt;
				       j <- newInt;
				       let w   = TermVar i
				           h   = TermVar j 
				       in
				       return (Abs w tau (Case (apply (Var w) (fst args)) z h z), Abs w tau (Case (apply (Var w) (snd args)) z' h z'))
				       }
			Cons x _ -> do{i <- newInt;
				       j <- newInt;
				       (g,g') <- lArrowArrow_construct_g tc gamma tau' tau' ([],[]) x y;
				       let w   = TermVar i
				           u   = TermVar j in
				       return (Abs w tau (Case1 (apply (Var w) (fst args)) (Cons (Var u) (Nil tau')) (App g  (Var u)) z),
					       Abs w tau (Case1 (apply (Var w) (snd args)) (Cons (Var u) (Nil tau')) (App g' (Var u)) z'))
				      }
      Arrow tau' tau'' -> let Abs x _ t = m1 
			      Just (u,u') = if Map.member x tc then Just (fst (trace "Map.!-check: lArrowArrow g-construct fst y (list case Arrow)" (tc Map.! x)),snd (trace "Map.!-check: lArrowArrow g-construct snd y (list case Arrow)" (tc Map.! x)))
					    else makePlusPair tau'
                          in
			  lArrowArrow_construct_g tc gamma tau tau'' (u:(fst args),u':(snd args)) t y

lFixArrow :: Cont -> [M ((Cont, Term -> Term),(TypedVar,TypedVar))]
lFixArrow gamma = 
    let l = findall typeCheckArrow (vars gamma) in
    map makeone l
    where makeone var = let Arrow tau1 tau2 = snd var in
			do {i <- newAux;
			    let x = TermVar i in
			    return ((updateVar (removeVar gamma (fst var)) x tau2,
			            \m -> subst m (App (Var (fst var)) (Bottom tau1)) x),
				    ((x,tau2),var))
		           }

lFixArrow_tc_update :: TermCont -> TermVar -> TypedVar -> TypedVar -> TermCont
lFixArrow_tc_update tc z x f = let Arrow t1 t2 = snd f 
				   Just (u,u') = if Map.member (fst x) tc then Just (fst (trace "Map.!-check: lFixArrow fst x" (tc Map.! (fst x))), snd (trace "Map.!-check: lFixArrow snd x" (tc Map.! (fst x))))
						 else makePlusPair (snd x) 
                               in 
			       Map.insert (fst f) (Abs z t1 u, Abs z t1 u') tc

------Ende Regeln der ersten Phase-------------

------Regeln fuer die zweite Phase-------------
aXStar :: Cont -> Typ -> Maybe (Term, (TermVar,Typ))
aXStar gamma tau = case findfirstSpecialType (varsStar gamma) tau of
                            Nothing -> Nothing
		            Just x  -> Just (Var (fst x), x)

aXStar_tc_update :: TermCont -> (TermVar,Typ) -> Maybe TermCont
aXStar_tc_update tc var = case makePlusPair (snd var) of
			    Nothing -> Nothing
			    Just p  -> Just (Map.insert (fst var) p tc)

laArrowStar1 :: Cont -> Maybe (M ((Cont, Term -> Term),((TermVar,Typ),(TermVar,Typ))))
laArrowStar1 gamma = case findfirst typeCheckArrow (varsStar gamma) of
                       Nothing                    -> Nothing
                       Just (f, Arrow tau1 tau2)  -> Just (do {i <- newAux;
							       let y = TermVar i in
							       return ((updateVarStar (removeVarStar gamma f) y tau2, \m -> subst m (App (Var f) (Bottom tau1)) y),((y, tau2),(f, Arrow tau1 tau2) ));
							     })
laArrowStar1_tc_update :: TermCont -> TermVar -> (TermVar,Typ) -> (TermVar,Typ) -> TermCont
laArrowStar1_tc_update tc x varIn varOut = case (snd varOut) of
					   Arrow tau1 _ ->
					     let Just (z,z') = if Map.member (fst varIn) tc then Just (fst (trace "Map.!-check: laArrowStar1 fst varIn" (tc Map.!(fst varIn))), snd (trace "Map.!-check: laArrowStar snd varIn" (tc Map.! (fst varIn))))
							       else makePlusPair $ snd varIn
					     in
					     Map.insert (fst varOut) (Abs x tau1 z, Abs x tau1 z') tc

laArrowStar2 :: Cont -> Maybe (M ((Cont, Term -> Term),([TypedVar],TypedVar)))
laArrowStar2 gamma = checkall (findall typeCheckArrow (vars gamma)) 
		     where checkall xs =
			       case xs of
				 []  -> Nothing
			         ((f, Arrow tau1 tau2):ys) -> case findfirstSpecialType (varsStar gamma) tau1 of
                                                                Nothing     -> checkall ys
								Just (x,_)  -> Just (do {i <- newAux;
										     let y = TermVar i in
										     return ((updateVarStar (removeVar gamma f) y tau2, \m -> subst m (App (Var f) (Var x)) y),([(x,tau1),(y,tau2)],(f,Arrow tau1 tau2)))
											})
-----------------------------------              x*          y*          f           -------- 
laArrowStar2_tc_update :: TermCont -> TermVar -> TypedVar -> TypedVar -> TypedVar -> TermCont
laArrowStar2_tc_update tc z x y f = let Just (u,u') = if (Map.member (fst y) tc) then Just (fst (trace "Map.!-check: laArrowStar2 fst y (TVar)" (tc Map.! (fst y))), snd (trace "Map.!-check: laArrowStar2 snd y (TVar)" (tc Map.! (fst y))))
						      else makePlusPair (snd y) 
                                        ana = laArrowStar2_typeAnalyse (snd x) ([],[]) in
					case (snd ana) of
					TVar t  -> let Just (a,a') = makePlusPair (TVar t) in
					           Map.insert (fst f) (Abs z (snd x) (Case1 (apply (Var z) (fst (fst ana))) a u u), Abs z (snd x) (Case1 (apply (Var z) (snd (fst ana))) a' u' u')) tc
					List t  -> Map.insert (fst f) (Abs z (snd x) (Case1 (apply (Var z) (fst (fst ana))) (Nil (snd y)) u u), Abs z (snd x) (Case1 (apply (Var z) (snd (fst ana))) (Nil (snd y)) u' u')) tc
														  
laArrowStar2_typeAnalyse :: Typ -> ([TermPlus],[TermPlus]) -> (([TermPlus],[TermPlus]),Typ)
laArrowStar2_typeAnalyse tau args = case tau of
				    TVar t       -> (args, tau)
				    Arrow t1 t2 -> case makePlusPair t1 of
						   Just (x,y) -> laArrowStar2_typeAnalyse t2 (x:(fst args), y:(snd args))
				    List t      -> (args, tau)

lIStar :: Cont -> Typ ->  Maybe (M ((Cont, Term -> Term),(TypedVar,TypedVar)))
lIStar gamma tau = case findfirst typeCheckList (varsStar gamma) of
                     Nothing           -> Nothing
		     Just (l,List tau') -> Just (do {i <- newInt;
						    let h = TermVar i in
						    return ((updateVarStar (removeVarStar gamma l) h tau',
							     \m -> subst m (Case (Var l) (Bottom tau') h (Var h)) h),
							    ((h, tau'),(l,List tau')))
						    })

lIStar_tc_update tc h l = let Just (u,u') = if Map.member (fst h) tc then Just (fst (trace "Map.!-check: lIStar fst h" (tc Map.!(fst h))), snd (trace "Map.!-check: lIStar snd h" (tc Map.!(fst h))))
					    else makePlusPair $ snd h
			  in
			  Map.insert (fst l) (Cons u (Nil (snd h)), Cons u' (Nil (snd h))) tc

lPStar :: Cont -> Maybe (M ((Cont, Term -> Term),([TypedVar],TypedVar)))
lPStar gamma = let l = findfirst typeCheckPair (varsStar gamma) in
	            case l of
		      Nothing -> Nothing
		      Just (p, TPair tau1 tau2) ->
		           Just (do {i <- newInt;
			 	     j <- newInt;
				     k <- newInt;
				     l <- newInt;
				     let x = TermVar i
				         y = TermVar j
				         u = TermVar k
				         v = TermVar l in
				     return ((updateVarStar (updateVarStar (removeVarStar gamma p) x tau1) y tau2,
				             \m -> subst (subst m (PCase (Var p) u v (Var u)) x) (PCase (Var p) u v (Var v)) y),
					     ([(x,tau1),(y,tau2)],(p,TPair tau1 tau2)))
				    })

lPStar_tc_update :: TermCont -> [TypedVar] -> TypedVar -> TermCont
lPStar_tc_update tc varIn p = let [x,y] = varIn 
				  Just (z,z') = if Map.member (fst x) tc then Just (fst (trace "Map.!-check: lPStar fst x" (tc Map.! (fst x))), snd (trace "Map.!-check: lPStar snd x" (tc Map.! (fst x))))
						else makePlusPair $ snd x
				  Just (u,u') = if Map.member (fst y) tc then Just (fst (trace "Map.!-check: lPStar fst y" (tc Map.! (fst y))), snd (trace "Map.!-check: lPStar snd y" (tc Map.! (fst y))))
						else makePlusPair $ snd y
			      in
                              Map.insert (fst p) (Pair z u, Pair z' u') tc

lEStar1 :: Cont -> Typ -> Maybe (M ((Cont, Term -> Term),(TypedVar,TypedVar)))
lEStar1 gamma tau = case findfirst typeCheckEither (varsStar gamma) of
                    Nothing -> Nothing
                    Just (e, TEither tau1 tau2) ->
		         Just (do {i <- newInt;
			   	   j <- newInt;
				   let x = TermVar i
			               y = TermVar j in
				   return ((updateVarStar (removeVarStar gamma e) x tau1,
					   \m -> subst m (ECase (Var e) x (Var x) y (Bottom tau1)) x),
					   ((x,tau1),(e,TEither tau1 tau2)))
				  })

lEStar1_tc_update :: TermCont -> TypedVar -> TypedVar -> TermCont
lEStar1_tc_update tc x e = let Just (z,z') = if Map.member (fst x) tc then Just (fst (trace "Map.!-check: lEStar1 fst x" (tc Map.! (fst x))), snd (trace "Map.!-check: lEStar1 snd x" (tc Map.! (fst x))))
					     else makePlusPair $ snd x
			   in
			   Map.insert (fst e) (Left z, Left z') tc

lEStar2 :: Cont -> Typ -> Maybe (M ((Cont, Term -> Term),(TypedVar,TypedVar)))
lEStar2 gamma tau = case findfirst typeCheckEither (varsStar gamma) of
                    Nothing -> Nothing
                    Just (e, TEither tau1 tau2) ->
		         Just (do {i <- newInt;
			   	   j <- newInt;
				   let x = TermVar i
			               y = TermVar j in
				   return ((updateVarStar (removeVarStar gamma e) y tau2,
					   \m -> subst m (ECase (Var e) x (Bottom tau1) y (Var y)) y),
					   ((y,tau2),(e,TEither tau1 tau2)))
				  })

lEStar2_tc_update :: TermCont -> TypedVar -> TypedVar -> TermCont
lEStar2_tc_update tc y e = let Just (z,z') = if Map.member (fst y) tc then Just (fst (trace "Map.!-check: lEStar2 fst y" (tc Map.! (fst y))), snd (trace "Map.!-check: lEStar2 snd y" (tc Map.! (fst y))))
					     else makePlusPair $ snd y
                           in
			   Map.insert (fst e) (Right z, Right z') tc

------------------- Der Algorithmus -------------------------

--Bemerkung: Pointed-Checks werden durch die Regelreihenfolge so weit als moeglich vermieden. ((LFix) und (RFix) stehen weit oben)

alg :: Cont -> Typ -> TermCont -> M (Term,TermCont)
alg gamma tau termCont = do track (makeTrackString "Start Conf" gamma tau)
			    alg1 gamma tau termCont

alg1 :: Cont -> Typ -> TermCont -> M (Term,TermCont)
alg1 = alg1_RFix

alg1_RFix :: Cont -> Typ -> TermCont -> M (Term,TermCont)
alg1_RFix gamma tau termCont = case rFix gamma tau of
		               Nothing -> alg1_RAllStar gamma tau termCont
			       Just t  -> do track ((makeTrackString "RFix" gamma tau) ++ "  !!END OF BRANCH!!")
				             return (t,termCont)
				      
alg1_RAllStar :: Cont -> Typ -> TermCont -> M (Term,TermCont)
alg1_RAllStar gamma tau termCont = case rAllStar gamma tau of
			           Nothing                -> alg1_RAll gamma tau termCont
			           Just (gamma', tau', f) -> do track (makeTrackString "RAllStar" gamma' tau')
								(t,c) <- (alg1 gamma' tau' termCont)
					              	        return (f t, c)
							      
alg1_RAll :: Cont -> Typ -> TermCont -> M (Term,TermCont)
alg1_RAll gamma tau termCont = case rAll gamma tau of
		               Nothing                -> alg1_LFix gamma tau termCont
			       Just (gamma', tau', f) -> do track (makeTrackString "RAll" gamma' tau')
							    (t,c) <- (alg1 gamma' tau' termCont)
							    return (f t,c)
		
alg1_LFix :: Cont -> Typ -> TermCont -> M (Term,TermCont)				     
alg1_LFix gamma tau termCont = case lFix gamma of
                               Nothing     -> alg1_LInt gamma tau termCont
                               Just gamma' -> do track (makeTrackString "LFix" gamma' tau)
					         alg1 gamma' tau termCont

alg1_LInt gamma tau termCont = case lInt gamma of
		               Nothing     -> alg1_RArrow gamma tau termCont
			       Just gamma' -> do track (makeTrackString "LInt" gamma' tau)
				                 alg1 gamma' tau termCont

alg1_RArrow :: Cont -> Typ -> TermCont -> M (Term,TermCont)
alg1_RArrow gamma tau termCont = case rArrow gamma tau of 
			         Nothing           -> alg1_RI gamma tau termCont
			         Just (comp, tau') -> do {(gamma', f) <- comp;
							  track (makeTrackString "R->" gamma' tau');
							  (t,c) <- (alg1 gamma' tau' termCont);
							  return (f t,c)
							 }

alg1_RI :: Cont -> Typ -> TermCont -> M (Term,TermCont)
alg1_RI gamma tau termCont = case rI tau of
                             Nothing        -> alg1_LIArrow gamma tau termCont
                             Just (tau', f) -> do track (makeTrackString "RI" gamma tau')
						  (t,c) <- (alg1 gamma tau' termCont)
					          return (f t,c)
				           
alg1_LIArrow :: Cont -> Typ -> TermCont -> M (Term,TermCont)
alg1_LIArrow gamma tau termCont = case lIArrow gamma of
                                  Nothing   -> alg1_LI gamma tau termCont
			          Just comp -> do {((gamma',f),(g,k)) <- comp;
						   track (makeTrackString "LI->" gamma' tau);
                                                   (t,c) <- (alg1 gamma' tau termCont);
						   i <- newInt;
						   j <- newInt;
						   let l = TermVar i
						       h = TermVar j in
						   return (f t,lIArrow_tc_update c l h g k)
						  }

alg1_LI :: Cont -> Typ -> TermCont -> M (Term,TermCont)
alg1_LI gamma tau termCont = case lI gamma tau of
                             Nothing     -> alg1_LPArrow gamma tau termCont
                             Just comp -> do {((gamma',f),(h,l)) <- comp;
					      track (makeTrackString "LI" gamma' tau);
					      (t,c) <- (alg1 gamma' tau termCont);
					      return (f t, lI_tc_update c h l)
					     }

alg1_LPArrow gamma tau termCont = case lPArrow gamma of
			          Nothing    -> alg1_LP gamma tau termCont
                                  Just comp  -> do {((gamma',f),(g,h)) <- comp;
						    track(makeTrackString "LP->" gamma' tau);
						    (t,c) <- (alg1 gamma' tau termCont);
						    termCont' <- lPArrow_tc_update c g h;
						    return (f t, termCont')
						   }

alg1_LP gamma tau termCont = case lP gamma of
		             Nothing    -> alg1_LEArrow gamma tau termCont
                             Just comp  -> do {((gamma',f),(varIn,p)) <- comp;
					       track(makeTrackString "LP" gamma' tau);
					       (t,c) <- (alg1 gamma' tau termCont);
					       return (f t, lP_tc_update c varIn p)
					      }

alg1_LEArrow gamma tau termCont = case lEArrow gamma of
                                  Nothing   -> alg1_LE1 gamma tau termCont
                                  Just comp -> do {((gamma',f),(varIn,g)) <- comp;
						   track (makeTrackString "LE->" gamma' tau);
						   (t,c) <- (alg1 gamma' tau termCont);
						   termCont' <- lEArrow_tc_update c varIn g;
						   return (f t, termCont')
						  }

alg1_LE1 gamma tau termCont = case lE1 gamma tau of
			      Nothing   -> alg1_RP1 gamma tau termCont
			      Just comp -> do {((gamma',f),(x,e)) <- comp;
					   let subderivation =
					           do  track (makeTrackString "LE1" gamma' tau)
					               (t,c) <- (alg1 gamma' tau termCont);
					               return (f t, lE1_tc_update c x e)
					   in
					   choice subderivation (alg1_LE2 gamma tau termCont);
					  }

alg1_LE2 gamma tau termCont = case lE2 gamma tau of
			      Nothing   -> alg1_RP1 gamma tau termCont --should never be reached
			      Just comp -> do {((gamma',f),(y,e)) <- comp;
					       track (makeTrackString "LE2" gamma' tau);
					       (t,c) <- (alg1 gamma' tau termCont);
					       return (f t, lE2_tc_update c y e)
					      }

alg1_RP1 gamma tau termCont = case rP1 tau of
                              Nothing        -> alg1_RE1 gamma tau termCont
                              Just (tau', f) -> choice subderivation (alg1_RP2 gamma tau termCont)
	                                         where subderivation = do {track (makeTrackString "RP1" gamma tau');
									   (t,c) <- (alg1 gamma tau' termCont);
							                   return (f t, c)
									  }
  
alg1_RP2 gamma tau termCont = case rP2 tau of
		              Nothing        -> alg1_RE1 gamma tau termCont
                              Just (tau', f) -> do {track (makeTrackString "RP2" gamma tau');
						    (t,c) <- (alg1 gamma tau' termCont);
					            return (f t,c)
						   }

alg1_RE1 gamma tau termCont = case rE1 tau of
                              Nothing        -> alg1_LFixArrowStar gamma tau termCont
                              Just (tau', f) -> choice subderivation (alg1_RE2 gamma tau termCont)
			                        where subderivation = do {track (makeTrackString "RE1" gamma tau');
									  (t,c) <- (alg1 gamma tau' termCont);
							                  return (f t,c)
									 }
									  
alg1_RE2 gamma tau termCont = case rE2 tau of
		              Nothing        -> alg1_LFixArrowStar gamma tau termCont
                              Just (tau', f) -> do {track (makeTrackString "RE2" gamma tau');
						    (t,c) <- (alg1 gamma tau' termCont);
					            return (f t,c)
						   }
					
alg1_LFixArrowStar :: Cont -> Typ -> TermCont -> M (Term,TermCont)
alg1_LFixArrowStar gamma tau termCont = foldr choice (alg1_LArrowArrow gamma tau termCont) (map trysubderivations (lFixArrowStar gamma))
			              where trysubderivations = \l -> do {((gamma', f),(y,g)) <- l; 
									  track (makeTrackString "LFix->*" gamma' tau);
									  (t,c) <- (alg2 gamma' tau termCont);
									  i <- newInt;
									  let x = TermVar i in
								          return (f t, lFixArrowStar_tc_update c x y g)
									 }

alg1_LArrowArrow :: Cont -> Typ -> TermCont -> M (Term,TermCont)
alg1_LArrowArrow gamma tau termCont = 
     foldr choice (alg1_LFixArrow gamma tau termCont) (map trysubderivations (lArrowArrow gamma))
     where trysubderivations = \l -> do {(((gamma1, tau1), gamma2, f),([w,y],g)) <- l;
					 track (makeTrackString "L->-> (fst)" gamma1 tau1);
					 track (makeTrackString "L->-> (snd)" gamma2 tau);
					 (t1,c1) <- (alg1 gamma1 tau1 termCont);
					 (t2,c2) <- (alg2 gamma2 tau termCont);
					 termCont' <- lArrowArrow_tc_update (Map.union c1 c2) gamma t1 w y g;
					 return (f t1 t2, termCont')
					}

alg1_LFixArrow :: Cont -> Typ -> TermCont -> M (Term,TermCont)
alg1_LFixArrow gamma tau termCont = 
     foldr choice (do {track "LFix->:  !!FAIL!!"; abort}) (map trysubderivations (lFixArrow gamma))
     where trysubderivations = \l -> do {((gamma', f),(x,g)) <- l;
					 track (makeTrackString "LFix->" gamma' tau);
					 (t,c) <- (alg1 gamma' tau termCont);
					 i <- newInt;
					 let z = TermVar i in
					 return (f t,lFixArrow_tc_update c z x g)
					}
--alg1_End gamma tau = return (GoalTerm gamma tau)

alg2 :: Cont -> Typ -> TermCont -> M (Term,TermCont)
alg2 = alg2_AXStar

alg2_AXStar :: Cont -> Typ -> TermCont -> M (Term,TermCont)
alg2_AXStar gamma tau termCont = case aXStar gamma tau of
                                 Nothing     -> alg2_LaArrowStar1 gamma tau termCont
                                 Just (t,v)  -> do track ((makeTrackString "AX*" gamma tau) ++ "  !!END OF BRANCH!!")
                                                   case aXStar_tc_update termCont v of
                                                     Nothing -> abort
                                                     Just tc -> return (t, tc)

alg2_LaArrowStar1 :: Cont -> Typ -> TermCont -> M (Term,TermCont)
alg2_LaArrowStar1 gamma tau termCont = case laArrowStar1 gamma of
				       Nothing -> alg2_LaArrowStar2 gamma tau termCont
				       Just (comp) 
					       -> do {((gamma', f),(varIn,varOut)) <- comp;
						      track (makeTrackString "La->*1" gamma' tau);
						      (t,c) <- (alg2 gamma' tau termCont);
						      i <- newInt;
						      let x = TermVar i in
						      return (f t, laArrowStar1_tc_update c x varIn varOut)
						     }

alg2_LaArrowStar2 :: Cont -> Typ -> TermCont -> M (Term,TermCont)
alg2_LaArrowStar2 gamma tau termCont = case laArrowStar2 gamma of
				       Nothing   -> alg2_LIStar gamma tau termCont
				       Just comp -> do {((gamma', f),([x,y],g)) <- comp;
							track (makeTrackString "La->*2" gamma' tau);
							(t,c) <- (alg2 gamma' tau termCont);
							i <- newInt;
							let u = TermVar i in
							return (f t, laArrowStar2_tc_update c u x y g)
						       }

alg2_LIStar :: Cont -> Typ -> TermCont -> M (Term,TermCont)
alg2_LIStar gamma tau termCont = case lIStar gamma tau of
                                 Nothing   -> alg2_LPStar gamma tau termCont
			         Just comp -> do {((gamma', f),(h,l)) <- comp;
						  track (makeTrackString "LI*" gamma' tau);
						  (t,c) <- (alg2 gamma' tau termCont);
						  return (f t, lIStar_tc_update c h l)
						 }

alg2_LPStar gamma tau termCont = case lPStar gamma of
			          Nothing   -> alg2_LEStar1 gamma tau termCont
			          Just comp -> do {((gamma', f),(h,p)) <- comp;
						   track (makeTrackString "LP*2" gamma' tau);
						   (t,c) <- (alg2 gamma' tau termCont);
						   return (f t, lPStar_tc_update c h p)
						  }

alg2_LEStar1 gamma tau termCont = case lEStar1 gamma tau of
			         Nothing   -> do {track "LE*1: FAIL";
						  abort
						 }
			         Just comp -> do {((gamma',f),(x,e)) <- comp;
						  let subderivation =
					                 do {track (makeTrackString "LE*1" gamma' tau);
					                     (t,c) <- (alg2 gamma' tau termCont);
							     return (f t, lEStar1_tc_update c x e)
							    }
						  in
						  choice subderivation (alg2_LEStar2 gamma tau termCont)
						 }

alg2_LEStar2 gamma tau termCont = case lEStar2 gamma tau of
			          Nothing   -> do {track "LE*2: FAIL";
						   abort
						  }
			          Just comp -> do {((gamma',f),(y,e)) <- comp;
						   track (makeTrackString "LE*2" gamma' tau);
						   (t,c) <- (alg2 gamma' tau termCont);
						   return (f t, lEStar2_tc_update c y e)
						  }

--------END Algorithm ---------

makeTrackString :: String -> Cont -> Typ -> String
makeTrackString = trackRules 

trackAll rule gamma tau = rule ++ ": " ++ showCont gamma ++ ", Type = " ++ showTyp tau
trackRules rule gamma tau = rule

getTerm tau = do printTyp tau
		 putStr "\n"
	         case runM $ alg emptyCont tau emptyTermCont of
	           Nothing             -> putStr "No Term."
		   Just (result,debug) -> do putStr ("    " ++ (foldr (\x -> \y -> x ++ "\n    " ++ y) "\n" debug))
					     printResult (fst result)

getComplete tau = do {printTyp tau;
		      putStr "\n";
		      case runM $ alg emptyCont tau emptyTermCont of
		      Nothing             -> putStr "No Term."
		      Just (result,debug) -> do {putStr ("    " ++ (foldr (\x -> \y -> x ++ "\n    " ++ y) "\n" debug));
						 printResult (fst result);
						 printUsedTermCont result;
						}
		     }

getWithDebug tau = do {printTyp tau;
		      putStr "\n";
		      case runM $ alg emptyCont tau emptyTermCont of
		      Nothing             -> putStr "No Term."
		      Just (result,debug) -> do {putStr ("    " ++ (foldr (\x -> \y -> x ++ "\n    " ++ y) "\n" debug));
						 printResult (fst result);
						 printTermCont (snd result);
						 printUsedTermCont result;						 
						}
		     }

printUsedTermCont :: (Term, TermCont) -> IO()
printUsedTermCont p =
    let (t,tc) = p in
    do {putStr "Wahl der abstrahierten Variablen:\n\n";
	putStr (showUsedTermCont t tc)
       }

showUsedTermCont :: Term -> TermCont -> String
showUsedTermCont t tc =
        case t of
	TAbs _ t'    -> showUsedTermCont t' tc
	Abs v tau t' -> case Map.findWithDefault (Bottom tau,Bottom tau) v tc of
	                (Bottom _, Bottom _) -> case makePlusPair tau of
		                                Nothing     -> "ERROR."
		                                Just (x,x') ->    (showTerm (Var v)) ++ "  = " ++ (showTermPlus False x) ++ "\n"
		                                               ++ (showTerm (Var v)) ++ "' = " ++ (showTermPlus True x')  ++ "\n\n"
							       ++ (showUsedTermCont t' tc)
		        (x,x')               ->    (showTerm (Var v)) ++ "  = " ++ (showTermPlus False x)  ++ "\n"
		                                ++ (showTerm (Var v)) ++ "' = " ++ (showTermPlus True x')   ++ "\n\n" 
						++ (showUsedTermCont t' tc)
--	Abs v tau t' -> if Map.member v tc 
--	                then case makePlusPair tau of
--                            Nothing     -> "ERROR."
--                             Just (x,x') ->    (showTerm (Var v)) ++ "  = " ++ (showTermPlus False x) ++ "\n"
--                                           ++ (showTerm (Var v)) ++ "' = " ++ (showTermPlus True x')  ++ "\n\n"
--                                            ++ (showUsedTermCont t' tc)
--		        else let (x,x') = (tc Map.! v) in
--                                (showTerm (Var v)) ++ "  = " ++ (showTermPlus False x)  ++ "\n"
--                            ++ (showTerm (Var v)) ++ "' = " ++ (showTermPlus True x')   ++ "\n\n" 
--                             ++ (showUsedTermCont t' tc)

	_            -> "Nothing else is required.\n\n"

printTermCont :: TermCont -> IO() 
printTermCont tc = putStr ("Anahl der Eintraege: " ++ (show (Map.size tc)) ++ "\n\n" ++ (showTermContList (Map.toList tc)))

showTermContList :: [(TermVar,(TermPlus,TermPlus))] -> String
showTermContList l = case l of
		     []             -> "Nothing left.\n"
		     (v,(x,x')):xs  ->   (showTerm (Var v)) ++ "  = " ++ (showTermPlus False x) ++ "\n"
			               ++ (showTerm (Var v)) ++ "' = " ++ (showTermPlus True x')  ++ "\n\n"
			               ++ (showTermContList xs)

--testWithAll tau = do printTyp tau
--		     case runMAll $ alg1 emptyCont tau of
--		       Nothing             -> putStr "No Term."
--		       Just (result,debug) -> do putStr (foldr (\x -> \y -> x ++ "\n" ++ y) "" debug)
--						 putStr (showTerm result)




printResult ::  Term -> IO ()
printResult t = putStr ("Ausgabe-Term: " ++ (showTerm t) ++ "\n\n")

printTyp :: Typ -> IO ()
printTyp t = putStr ("Eingabe-Typ:  " ++ showTyp t ++ "\n")

showCont :: Cont -> String
showCont gamma = let showVars = 
			 let vs = vars gamma in 
			 case vs of
			  [] -> "]"
			  _  -> foldr (\x -> \y -> x ++ "," ++ y) "\b]" (map (\v -> showTerm (Var (fst v)) ++ "::" ++ showTyp (snd v)) (vs))
		     showVarsStar = 
			 let vs = varsStar gamma in
		         case vs of
			   [] -> "]"
			   _  -> foldr (\x -> \y -> x ++ "," ++ y) "\b]" (map (\v -> showTerm (Var (fst v)) ++ "::" ++ showTyp (snd v)) (vs)) 
		in
		"Cont = {vars = [" ++ showVars ++ ", varsStar = [" ++ showVarsStar ++ "}"

showTerm :: Term -> String
showTerm t = 
    case t of
    Extra _       -> "ERROR. Extra as Term."
    Case1 _ _ _ _ -> "ERROR. Case1 as Term."
    _             -> (showAbsTerm t showTerm)

showTermPlus :: Bool -> TermPlus -> String
showTermPlus strip t = 
    case t of
    Extra (PlusElem (TypVar i) j) -> if strip == False
			    then "(p" ++ (show i) ++ "(" ++ show j ++ "))"
			    else "(p" ++ (show i) ++ "'(" ++ show j ++ "))"
    _                    -> if strip == False 
			    then showAbsTerm t (showTermPlus False)
			    else showAbsTerm t (showTermPlus True )

showAbsTerm :: (AbsTerm a) -> ((AbsTerm a) -> String) -> String
showAbsTerm t showTerm = case t of
	       Var (TermVar i)      -> 'x':(show i)
	       Abs v _ t'           -> "(\\" ++ (showTerm (Var v)) ++ "." ++ (showTerm t') ++ ")"
               App t1 t2            -> "(" ++ (showTerm t1) ++ " " ++ (showTerm t2) ++ ")"
               Nil _                -> "[]"
               Cons t1 t2           -> "(" ++ (showTerm t1) ++ ":" ++ (showTerm t2) ++ ")"
               Case t0 t1 v2 t2     -> "(case " ++ (showTerm t0) ++ " of {[] => " ++ (showTerm t1) ++ "; " ++ showTerm (Var v2) ++ ":_ => " ++ (showTerm t2) ++"})" 
	       Bottom _             -> "_|_"
               TAbs (TypVar i) t    -> (showTerm t)
	       Extra a              -> "No show-function implemented."
	       Case1 t1 t2 t3 t4    -> "(case " ++ (showTerm t1) ++ " of {" ++ (showTerm t2) ++ " => " ++ (showTerm t3) ++ "; _ => " ++ (showTerm t4) ++ "})"
               Pair t1 t2           -> "(" ++ showTerm t1 ++ "," ++ showTerm t2 ++ ")"
	       PCase t0 v1 v2 t1    -> "(case " ++ showTerm t0 ++ " of {(" ++ showTerm (Var v1) ++ "," ++ showTerm (Var v2) ++ ") => " ++ showTerm t1 ++ "})"
	       ECase t0 v1 t1 v2 t2 -> "(case " ++ showTerm t0 ++ " of { Left(" ++ showTerm (Var v1) ++ ") => " ++ showTerm t1 ++ "; Right(" ++ showTerm (Var v2) ++ ") => " ++ showTerm t2 ++ "})"
               Left t               -> "Left(" ++ showTerm t ++ ")"
               Right t              -> "Right(" ++ showTerm t ++ ")"
               Zero                 -> "0" 																			

showTyp :: Typ -> String
showTyp t = case t of
              TVar (TypVar i)    -> ('v':(show i))
              Arrow t1 t2        -> "(" ++ showTyp t1 ++ " -> " ++ showTyp t2 ++ ")"
              All v t            -> "\\" ++ showTyp (TVar v) ++ "." ++ showTyp t
              AllStar v t        -> "\\" ++ showTyp (TVar v) ++ "." ++ showTyp t
              List t             -> "[" ++ showTyp t ++ "]"
              Int                -> "Int"
              TPair t1 t2        -> "(" ++ showTyp t1 ++ "," ++ showTyp t2 ++ ")"
              TEither t1 t2      -> "(" ++ showTyp t1 ++ "+" ++ showTyp t2 ++ ")"

parseTerm :: String -> Typ
parseTerm str = TVar (TypVar 0) --dummy



--testing fuction
testTerm tau = case runM $ alg emptyCont tau emptyTermCont of
		 Nothing    -> Nothing
                 Just (x,_) -> Just (fst x)

getIt typstring = getComplete $ parseType typstring
