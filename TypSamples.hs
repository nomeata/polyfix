module TypSamples where

samples = 
    [ "a" 					-- 1
    , "[a] -> [a]"
    , "(a -> b) -> b"
    , "([a]-> b) -> b"
    , "[b] -> (a -> b) -> b" 			-- 5
    , "a -> (a -> b)-> b"
    , "(((a -> b) -> b) -> b) -> b"
    , "((( a -> (b -> b)) -> b) -> b) -> b"
    , "(a -> b) -> ((b -> c) -> c)"
    , "(a -> [b]) -> b"                         -- 10
    , "(b -> (a -> b)) -> b"
    , "(((c -> (a -> [b])) -> b) -> c) -> (((b -> [c]) -> (c -> d) -> [d]))"
    ]
exSamples = 
    [ "(a -> Int) -> (Int -> Int)"              -- Ex 1
    ]
