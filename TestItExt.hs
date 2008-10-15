import Test.HUnit
import ExFindExtended
import Prelude hiding (Either(..))

-------------------------------------------------------------------------------------------------
---TestBeispiele fuer ExFind---------------------------------------------------------------------
---um alle Tests auszufuehren  runTestTT tests  aufrufen-----------------------------------------
---fuer einzelne Tests runTestTT test1  bzw. die entsprechenden Nummer statt 1-------------------
---fuer Anzeige der bei der Ableitung benutzten Regeln  getTerm bsp1  bzw. entsprechende Nr------
-------------------------------------------------------------------------------------------------

---shortcuts---
fAll i = All (TypVar i)
fAllStar i = AllStar (TypVar i)
tau1 `arrow` tau2 = Arrow tau1 tau2
var i = TVar (TypVar i)

--Beispiele:

-- RFix
bsp1 = fAll 1 (var 1)
-- RAll, R->, RI, RFix
bsp2 = fAll 1 (List (var 1) `arrow` List (var 1))
-- RAll, RAllStar, R->, LFixArrowStar, AxStar
bsp3 = fAll 1 (fAllStar 2 ((var 1 `arrow` var 2) `arrow` var 2))
-- RAll, RAllStar, R->, LIArrow, LFixArrowStar, AxStar
bsp4 = fAll 1 (fAllStar 2 ((List (var 1) `arrow` var 2) `arrow` var 2))

-- test for LI
-- RAll, RAllStar, R->, R->, LI, LFixArrowStar, AxStar
bsp5 = fAll 1 (fAllStar 2 ((List (var 2)) `arrow` ((var 1 `arrow` var 2) `arrow` var 2)))

-- test for LFix
-- RAll, RAllStar, R->, R->, LFix, LFixArrowStar, AxStar
bsp6 = fAll 1 (fAllStar 2 ( var 1 `arrow` ((var 1 `arrow` var 2) `arrow` var 2)))

-- test for L->->
-- RAll, RAllStar, R->, L->-> (fst: LFix->*, Ax*) (snd: Ax*)
bsp7 = fAll 1 (fAllStar 2 (((( var 1 `arrow` var 2) `arrow` var 2) `arrow` var 2) `arrow` var 2))

-- test for La->*1
-- RAll, RAllStar, R->, L->-> (fst: LFix->*, La->*1, Ax*) (snd: Ax*)
bsp8 = fAll 1 (fAllStar 2 (((( var 1 `arrow` (var 2 `arrow` var 2)) `arrow` var 2) `arrow` var 2) `arrow` var 2))

-- test for La->*2
-- RAll, RAllStar, R->, R->, LFix->*, La->*2, Ax*
bsp9 = fAll 1 (fAllStar 2 (fAllStar 3 (((var 1 `arrow` var 2) `arrow` ((var 2 `arrow` var 3) `arrow` var 3)))))

bsp10 = fAll 1 (fAllStar 2 ((var 1 `arrow` (List (var 2))) `arrow` var 2))

-- test for LFix
-- RAll, RAllStar, R->, LFix->, LFix->*, Ax*
bsp11 = fAll 1 (fAllStar 2 ((var 2 `arrow` (var 1 `arrow` var 2)) `arrow` var 2))

bsp12 = fAll 1 (fAllStar 2 (fAllStar 3 (fAllStar 4 ((((var 3 `arrow` (var 1 `arrow` (List (var 2)))) `arrow` var 2) `arrow` var 3) `arrow` (((var 2 `arrow` (List (var 3))) `arrow` (var 3 `arrow` var 4) `arrow` (List (var 4))))))))

-----new examples for the extended algorithm-------
--test for LInt
--RAll, R->, R->, LInt, LFix->*, Ax*
bspEx1 = fAll 1 ((var 1 `arrow` Int) `arrow` (Int `arrow` Int))

--test for LP->
--RAll, R->, LP->, LFix->*, La->*1, Ax*
bspEx2 = fAll 1 (((TPair (var 1) Int) `arrow` Int) `arrow` Int)

--test for LP
--RAll, R->, LP, LInt, LFix->*, Ax*
bspEx3 = fAll 1 ((TPair (var 1 `arrow` Int) Int) `arrow` Int)

--test for LE->
--RAll, R->, LE->, LFix->*, Ax*
bspEx4 = fAll 1 (((TEither (var 1) Int) `arrow` Int) `arrow` Int)

--test for LE->
--RAll, R->, LE->, LFix->*, Ax*
bspEx5 = fAll 1 (((TEither Int (var 1)) `arrow` Int) `arrow` Int)

--test for LE1
bspEx6 = fAll 1 ((TEither (var 1 `arrow` Int) Int) `arrow` Int)

--test for LE2
bspEx7 = fAll 1 ((TEither Int (var 1 `arrow` Int)) `arrow` Int)

--another test for LE1
bspEx8 = fAll 1 (fAllStar 2 ((TEither (var 1 `arrow` var 2) (var 1 `arrow` Int)) `arrow` ((var 2 `arrow` Int) `arrow` Int)))

--test for RP1
bspEx9 = fAll 1 (TPair (var 1) (var 1))

--test for RP2
bspEx10 = fAll 1 (TPair Int (var 1))


--test for RE1
bspEx11 = fAll 1 (TEither (var 1) (var 1))

--test for RE2
bspEx12 = fAll 1 (TEither Int (var 1))

--test for LP*1
bspEx13 = fAll 1 ((var 1 `arrow` (TPair Int Int)) `arrow` Int)

--test for LP*2
bspEx14 = fAll 1 (fAllStar 2 ((var 1 `arrow` (TPair (var 2) Int)) `arrow` Int))

--test for LE*1
bspEx15 = fAll 1 ((var 1 `arrow` (TEither Int Int)) `arrow` Int)

--test for LE*2
bspEx16 = fAll 1 (fAllStar 2 ((var 1 `arrow` (TEither (var 2) Int)) `arrow` Int))



-----test cases using HUnit Test--------

run test = runTestTT test


test1 = TestCase $ assertEqual "a.a: " (Just (Bottom (All (TypVar 1) (TVar (TypVar 1))))) (testTerm bsp1)
test2 = TestCase $ assertEqual 
	             "a.[a] -> [a]:" 
                     (Just (TAbs (TypVar 1) (Abs (TermVar 1) (List (TVar (TypVar 1))) (Cons (Bottom (TVar (TypVar 1))) (Nil (TVar (TypVar 1)))))))
		     (testTerm bsp2)

test3 = TestCase $ assertEqual 
	             "a.b.(a -> b) -> b:"
		     (Just (TAbs (TypVar 1) (TAbs (TypVar 2) (Abs (TermVar 1) (Arrow (TVar (TypVar 1)) (TVar (TypVar 2))) (App (Var (TermVar 1)) (Bottom (TVar (TypVar 1))))))))
		     (testTerm bsp3)

test4 = TestCase $ assertEqual
	             "a.b.([a] -> b) -> b:"
		     (Just (TAbs (TypVar 1) (TAbs (TypVar 2) (Abs (TermVar 1) (Arrow (List (TVar (TypVar 1))) (TVar (TypVar 2))) (App (Abs (TermVar 2) (TVar (TypVar 1)) (App (Var (TermVar 1)) (Cons (Var (TermVar 2)) (Nil (TVar (TypVar 1)))))) (Bottom (TVar (TypVar 1))))))))
		     (testTerm bsp4)

test5 = TestCase $ assertEqual
	             "a.b.[b] -> (a -> b) -> b"
		     (Just (TAbs (TypVar 1) (TAbs (TypVar 2) (Abs (TermVar 1) (List (TVar (TypVar 2))) (Abs (TermVar 2) (Arrow (TVar (TypVar 1)) (TVar (TypVar 2))) (App (Var (TermVar 2)) (Bottom (TVar (TypVar 1)))))))))
		     (testTerm bsp5)

test6 = TestCase $ assertEqual
	             "a.b.a -> (a -> b) -> b"
		     (Just (TAbs (TypVar 1) (TAbs (TypVar 2) (Abs (TermVar 1) (TVar (TypVar 1)) (Abs (TermVar 2) (Arrow (TVar (TypVar 1)) (TVar (TypVar 2))) (App (Var (TermVar 2)) (Bottom (TVar (TypVar 1)))))))))
		     (testTerm bsp6)
		     
test7 = TestCase $ assertEqual
	             "a.b.(((a -> b) -> b) -> b) -> b"
		     (Just (TAbs (TypVar 1) (TAbs (TypVar 2) (Abs (TermVar 1) (Arrow (Arrow (Arrow (TVar (TypVar 1)) (TVar (TypVar 2))) (TVar (TypVar 2))) (TVar (TypVar 2))) (App (Var (TermVar 1)) (Abs (TermVar 2) (Arrow (TVar (TypVar 1)) (TVar (TypVar 2))) (App (Var (TermVar 2)) (Bottom (TVar (TypVar 1))))))))))
		     (testTerm bsp7)

test8 = TestCase $ assertEqual
	             "a.b.(((a -> (b -> b)) -> b) -> b) -> b"
		     (Just (TAbs (TypVar 1) (TAbs (TypVar 2) (Abs (TermVar 1) (Arrow (Arrow (Arrow (TVar (TypVar 1)) (Arrow (TVar (TypVar 2)) (TVar (TypVar 2)))) (TVar (TypVar 2))) (TVar (TypVar 2))) (App (Var (TermVar 1)) (Abs (TermVar 2) (Arrow (TVar (TypVar 1)) (Arrow (TVar (TypVar 2)) (TVar (TypVar 2)))) (App (App (Var (TermVar 2)) (Bottom (TVar (TypVar 1)))) (Bottom (TVar (TypVar 2))))))))))
		     (testTerm bsp8)

test9 = TestCase $ assertEqual
	             "a.b.(a -> b) -> (b -> c) -> c"
		     (Just (TAbs (TypVar 1) (TAbs (TypVar 2) (TAbs (TypVar 3) (Abs (TermVar 1) (Arrow (TVar (TypVar 1)) (TVar (TypVar 2))) (Abs (TermVar 2) (Arrow (TVar (TypVar 2)) (TVar (TypVar 3))) (App (Var (TermVar 2)) (App (Var (TermVar 1)) (Bottom (TVar (TypVar 1)))))))))))
		     (testTerm bsp9)

test10 = TestCase $ assertEqual
	              "a.b.(a -> [b]) -> b"
		      (Just (TAbs (TypVar 1) (TAbs (TypVar 2) (Abs (TermVar 1) (Arrow (TVar (TypVar 1)) (List (TVar (TypVar 2)))) (Case (App (Var (TermVar 1)) (Bottom (TVar (TypVar 1)))) (Bottom (TVar (TypVar 2))) (TermVar 2) (Var (TermVar 2)))))))
		      (testTerm bsp10)

test11 = TestCase $ assertEqual
	              "a.b.(b -> (a -> b)) -> b"
		      (Just (TAbs (TypVar 1) (TAbs (TypVar 2) (Abs (TermVar 1) (Arrow (TVar (TypVar 2)) (Arrow (TVar (TypVar 1)) (TVar (TypVar 2)))) (App (App (Var (TermVar 1)) (Bottom (TVar (TypVar 2)))) (Bottom (TVar (TypVar 1))))))))
		      (testTerm bsp11)

test12 = TestCase $ assertEqual
	              "a.b.c.d.((c -> (a -> [b]) -> b) -> c) -> (b -> [c]) -> (c -> d) -> [d]"
		      (Just (TAbs (TypVar 1) (TAbs (TypVar 2) (TAbs (TypVar 3) (TAbs (TypVar 4)
			       (Abs (TermVar 1) (Arrow (Arrow (Arrow (TVar (TypVar 3)) (Arrow (TVar (TypVar 1)) (List (TVar (TypVar 2))))) (TVar (TypVar 2))) (TVar (TypVar 3)))
				 (Abs (TermVar 2) (Arrow (Arrow (TVar (TypVar 2)) (List (TVar (TypVar 3)))) (Arrow (TVar (TypVar 3)) (TVar (TypVar 4))))
			       (Cons (App 
				       (App (Var (TermVar 2)) 
					 (Abs (TermVar 3) (TVar (TypVar 2)) 
				           (Cons (App (Var (TermVar 1)) (Abs (TermVar 5) 
									  (Arrow (TVar (TypVar 3)) (Arrow (TVar (TypVar 1)) (List (TVar (TypVar 2)))))
									  (Case (App (App (Var (TermVar 5)) (Bottom (TVar (TypVar 3)))) (Bottom (TVar (TypVar 1)))) (Bottom (TVar (TypVar 2))) (TermVar 7) (Var (TermVar 7)))
									)
						 ) 
				  (Nil (TVar (TypVar 3))))
				)) (Bottom (TVar (TypVar 3)))) (Nil (TVar (TypVar 4)))))))))))
		      (testTerm bsp12)

testList = [TestLabel "RFix-Test" test1, TestLabel "RAll,R->,RI-Test" test2, TestLabel "RAll*,LFix->*,Ax*-Test" test3, TestLabel "LI->-Test" test4, TestLabel "LI-Test" test5, TestLabel "LFix-Test" test6, TestLabel "L->->-Test" test7, TestLabel "La->*1" test8, TestLabel "La->*2" test9, TestLabel "LI*-Test" test10, TestLabel "LFix->-Test" test11, TestLabel "complex typ" test12 ]

tests = TestList testList

testEx1 = TestCase $ assertEqual
	               "a.(a -> Int) -> Int -> Int"
		       (Just (TAbs (TypVar 1) (Abs (TermVar 1) (Arrow (TVar (TypVar 1)) Int) (Abs (TermVar 2) Int (App (Var (TermVar 1)) (Bottom (TVar (TypVar 1))))))))
		       (testTerm bspEx1)

testEx2 = TestCase $ assertEqual
	               "a.((a,Int) -> Int) -> Int"
		       (Just (TAbs (TypVar 1) (Abs (TermVar 1) (Arrow (TPair (TVar (TypVar 1)) Int) Int) (App (App (Abs (TermVar 2) (TVar (TypVar 1)) (Abs (TermVar 3) Int (App (Var (TermVar 1))  (Pair (Var (TermVar 2)) (Var (TermVar 3)))))) (Bottom (TVar (TypVar 1)))) (Bottom Int)))))
		       (testTerm bspEx2)
testEx3 = TestCase $ assertEqual
	               "a.((a -> Int),Int) -> Int"
		       (Just (TAbs (TypVar 1) (Abs (TermVar 1) (TPair (Arrow (TVar (TypVar 1)) Int) Int) (App (PCase (Var (TermVar 1)) (TermVar 4) (TermVar 5) (Var (TermVar 4))) (Bottom (TVar (TypVar 1)))))))
		       (testTerm bspEx3)

testEx4 = TestCase $ assertEqual
	               "a.((a+Int) -> Int) -> Int"
		       (Just (TAbs (TypVar 1) (Abs (TermVar 1) (Arrow (TEither (TVar (TypVar 1)) Int) Int) (App (Abs (TermVar 2) (TVar (TypVar 1)) (App (Var (TermVar 1)) (Left (Var (TermVar 2))))) (Bottom (TVar (TypVar 1)))))))
		       (testTerm bspEx4)

testEx5 = TestCase $ assertEqual
	               "a.((Int+a) -> Int) -> Int"
		       (Just (TAbs (TypVar 1) (Abs (TermVar 1) (Arrow (TEither Int (TVar (TypVar 1))) Int) (App (Abs (TermVar 3) (TVar (TypVar 1)) (App (Var (TermVar 1)) (Right (Var (TermVar 3))))) (Bottom (TVar (TypVar 1)))))))
		       (testTerm bspEx5)

testEx6 = TestCase $ assertEqual
	               "a.((a -> Int) + Int) -> Int"
		       (Just (TAbs (TypVar 1) (Abs (TermVar 1) (TEither (Arrow (TVar (TypVar 1)) Int) Int) (App (ECase (Var (TermVar 1)) (TermVar 2) (Var (TermVar 2)) (TermVar 3) (Bottom (Arrow (TVar (TypVar 1)) Int))) (Bottom (TVar (TypVar 1)))))))
		       (testTerm bspEx6)

testEx7 = TestCase $ assertEqual
	               "a.(Int + (a -> Int)) -> Int"
		       (Just (TAbs (TypVar 1) (Abs (TermVar 1) (TEither Int (Arrow (TVar (TypVar 1)) Int)) (App (ECase (Var (TermVar 1)) (TermVar 4) (Bottom (Arrow (TVar (TypVar 1)) Int)) (TermVar 5) (Var (TermVar 5))) (Bottom (TVar (TypVar 1)))))))
		       (testTerm bspEx7)

testEx8 = TestCase $ assertEqual
	               "a.b.((a -> b) + (a -> Int)) -> (b -> Int) -> Int"
		       (Just (TAbs (TypVar 1) (TAbs (TypVar 2) (Abs (TermVar 1) (TEither (Arrow (TVar (TypVar 1)) (TVar (TypVar 2))) (Arrow (TVar (TypVar 1)) Int)) (Abs (TermVar 2) (Arrow (TVar (TypVar 2)) Int) (App (Var (TermVar 2)) (App (ECase (Var (TermVar 1)) (TermVar 3) (Var (TermVar 3)) (TermVar 4) (Bottom (Arrow (TVar (TypVar 1)) (TVar (TypVar 2))))) (Bottom (TVar (TypVar 1))))))))))
		       (testTerm bspEx8)

testEx9 = TestCase $ assertEqual
	               "a.(a,a)"
		       (Just (TAbs (TypVar 1) (Pair (Bottom (TVar (TypVar 1))) (Bottom (TVar (TypVar 1))))))
		       (testTerm bspEx9)

testEx10 = TestCase $ assertEqual
	               "a.(Int,a)"
		       (Just (TAbs (TypVar 1) (Pair (Bottom Int) (Bottom (TVar (TypVar 1))))))
		       (testTerm bspEx10)

testEx11 = TestCase $ assertEqual
	               "a.(a+a)"
		       (Just (TAbs (TypVar 1) (Left (Bottom (TVar (TypVar 1))) )))
		       (testTerm bspEx11)

testEx12 = TestCase $ assertEqual
	               "a.(a+a)"
		       (Just (TAbs (TypVar 1) (Right (Bottom (TVar (TypVar 1))))))
		       (testTerm bspEx12)

testEx13 = TestCase $ assertEqual
	               "a.(a -> (Int,Int)) -> Int"
		       (Just (TAbs (TypVar 1) (Abs (TermVar 1) (Arrow (TVar (TypVar 1)) (TPair Int Int)) (PCase (App (Var (TermVar 1)) (Bottom (TVar (TypVar 1)))) (TermVar 4) (TermVar 5) (Var (TermVar 5))))))
		       (testTerm bspEx13)

testEx14 = TestCase $ assertEqual
	               "a.b.(a -> (b,Int)) -> Int"
		       (Just (TAbs (TypVar 1) (TAbs (TypVar 2) (Abs (TermVar 1) (Arrow (TVar (TypVar 1)) (TPair (TVar (TypVar 2)) Int)) (PCase (App (Var (TermVar 1)) (Bottom (TVar (TypVar 1)))) (TermVar 4) (TermVar 5) (Var (TermVar 5)))))))
		       (testTerm bspEx14)

testEx15 = TestCase $ assertEqual
	               "a.(a -> (Int+Int)) -> Int"
		       (Just (TAbs (TypVar 1) (Abs (TermVar 1) (Arrow (TVar (TypVar 1)) (TEither Int Int)) (ECase (App (Var (TermVar 1)) (Bottom (TVar (TypVar 1)))) (TermVar 2) (Var (TermVar 2)) (TermVar 3) (Bottom Int)))))
		       (testTerm bspEx15)

testEx16 = TestCase $ assertEqual
	               "a.b.(a -> (b+Int)) -> Int"
		       (Just (TAbs (TypVar 1) (TAbs (TypVar 2) (Abs (TermVar 1) (Arrow (TVar (TypVar 1)) (TEither (TVar (TypVar 2)) Int)) (ECase (App (Var (TermVar 1)) (Bottom (TVar (TypVar 1)))) (TermVar 4) (Bottom (TVar (TypVar 2))) (TermVar 5) (Var (TermVar 5)))))))
		       (testTerm bspEx16)

exTestList = [TestLabel "LInt" testEx1, TestLabel "LP->" testEx2, TestLabel "LP" testEx3, TestLabel "LE-> (Left)" testEx4, TestLabel "LE-> (Right)" testEx5, TestLabel "LE1" testEx6, TestLabel "LE2" testEx7 , TestLabel "LE1 complex" testEx8, TestLabel "RP1" testEx9, TestLabel "RP2" testEx10, TestLabel "RE1" testEx11, TestLabel "RE2" testEx12, TestLabel "LP*1" testEx13, TestLabel "LP*2" testEx14, TestLabel "LE*1" testEx15, TestLabel "LE*2" testEx16]

exTests = TestList exTestList

allTests = TestList (testList ++ exTestList)


testbsp = ( fAll 1 ( ( ((List Int) `arrow` var 1 ) `arrow` Int ) `arrow` Int ) )
