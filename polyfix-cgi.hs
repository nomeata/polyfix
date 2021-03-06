module Main where

import ParseType (parseType')
import SimpleFT  (freeTheorem)
import Expr (specialize)
import ExFindExtended (getCompleteRaw, showTerm, showUsedTermCont)
import Language.Haskell.FreeTheorems.Parser.Haskell98 as FTP
import Language.Haskell.FreeTheorems
	( runChecks
	, check
	, filterSignatures
	, prettyTheorem
	, asTheorem
	, interpret
	, unfoldLifts
	, prettyUnfoldedLift
	, LanguageSubset(BasicSubset)
	)
import Term2Expr (term2Expr, termCond2Exprs, insertTermsInCondition)

import Network.CGI
import Data.ByteString.Lazy.UTF8 (fromString)
import Text.XHtml
import Control.Monad
import Data.Maybe
import Text.PrettyPrint.HughesPJ (render)
import qualified Data.Map as M
import Data.Generics

askDiv v e =  maindiv << (
	p << ( "Please enter a function type, prepended with a list of type variables, " +++
	       "whose relations should be allowed to be nonstrict, and a single dot.") +++ 	      p << ( input ! [name "type", value v] +++ " " +++
 	       submit "submit" "Generate Free Theorem and counter example" ) +++
	e
	)


askTypeForm = askDiv "a. (a -> b) -> b" noHtml

typeError typeStr err = askDiv typeStr (
	p << ("There was a problem parsing your type: " +++
  	      pre << err )
	)

generateResult typeStr typ = askDiv typeStr noHtml +++
	maindiv << (
	h3 << "The Free Theorem" +++
	(case ft_full of
		Left err -> p << "The full Free Theorem deriver failed:" +++
                            pre << err
                Right s  -> p << "For your type, the following Free Theorem holds:" +++
         	            pre << s
	) +++
	p << "Specializing relations to functions, canceling irrelvant terms and eta-reduction, this theorem can be written as:" +++
	pre << show ft_simple +++
	p << "Further specializing all types to (), all strict functions to id and all non-strict functions to const (), this theorem can be written as:" +++
	pre << show ft_simple_special
	) +++
	maindiv << (
	h3 << "The counter-example" +++
	( case counter_example of 
		Left err -> p << "No term could be derived: " +++ pre << err
		Right result ->
			p << ("By disregarding the strictness conditions for the chosen "+++
                              "relations, the following term is a counter example:" +++
                              pre << ("f = " ++ showTerm (fst result)) ) +++
			p << ("Whereas the abstraced variables are chosen as follows:" +++
                              pre << uncurry showUsedTermCont result) +++
			p << ("Inserting these defintions in the above theorem yields:" +++
			-- p << (show result) +++
			-- p << (show (term2Expr (fst result))) +++
			-- p << (show (termCond2Exprs (snd result))) +++
			      pre << (show (insertTermsInCondition result ft_simple_special))
				) 
			-- p << (gshow (insertTermsInCondition result (specialize ft_simple)))
	)) +++
	maindiv ( p << ("In the simplified theorems, the following custom haskell " +++
                        "functions might appear:") +++
		  pre << addDefs
	)
  where ft_full = let properType = "f :: " ++ case span (/='.') typeStr of
                                       (t,"")  -> t
                                       (_,_:t) -> t
		      either  = "data Either a b = Left a | Right b"
		      parse_input = unlines [either, properType]
		      (ds,es) = runChecks (parse parse_input >>= check)
                      [s]     = filterSignatures ds
		  in if null es
                     then case interpret ds BasicSubset s of
			Nothing -> Left "interpret returned nothing"
			Just i  -> Right $ render (prettyTheorem [] (asTheorem i)) ++
			      case unfoldLifts ds i of
				[] -> ""
				ls -> "\n\nWhereas the occuring lifts are defined as:\n\n "++
				      unlines (map (render . prettyUnfoldedLift []) ls)
                     else Left (unlines (map render es))
		    
	ft_simple = freeTheorem typ
	ft_simple_special = specialize ft_simple
        counter_example = getCompleteRaw typ
	
main = runCGI (handleErrors cgiMain)

cgiMain = do
	setHeader "Content-type" "text/xml; charset=UTF-8"
	
	mTypeStr <- getInput "type"

	
	let content = case mTypeStr of 
		Nothing      -> askTypeForm
                Just typeStr -> case parseType' typeStr of
			Left err  -> typeError typeStr err
			Right typ -> generateResult typeStr typ
	
	outputFPS $ fromString $ showHtml $
	       header (
		thetitle << "PolyFix" +++
		style ! [ thetype "text/css" ] << cdata cssStyle
	       ) +++
	       body ( form ! [method "POST", action "#"] << (
		thediv ! [theclass "top"] << (
			thespan ! [theclass "title"] << "PolyFix" +++
			thespan ! [theclass "subtitle"] << "Counter Examples for Free Theorems"
		) +++
		content +++
		maindiv ( p << ("?? 2008 Daniel Seidel und Joachim Breitner <" +++
			      hotlink "mailto:mail@joachim-breitner.de" << "mail@joachim-breitner.de" +++
			      ">")
			)       
		))

maindiv = thediv ! [theclass "main"]

cdata s = primHtml ("<![CDATA[\n"++ s ++ "\n]]>")

cssStyle = unlines 
        [ "body { padding:0px; margin: 0px; }"
        , "div.top { margin:0px; padding:10px; margin-bottom:20px;"
        , "              background-color:#efefef;"
        , "              border-bottom:1px solid black; }"
        , "span.title { font-size:xx-large; font-weight:bold; }"
        , "span.subtitle { padding-left:30px; font-size:large; }"
        , "div.main { border:1px dotted black;"
        , "                   padding:10px; margin:10px; }"
        , "div.submain { padding:10px; margin:11px; }"
        , "p.subtitle { font-size:large; font-weight:bold; }"
        , "input.type { font-family:monospace; }"
        , "input[type=\"submit\"] { font-family:monospace; background-color:#efefef; }"
        , "span.mono { font-family:monospace; }"
        , "pre { margin:10px; margin-left:20px; padding:10px;"
        , "          border:1px solid black; }"
        , "textarea { margin:10px; margin-left:20px; padding:10px;  }"
        , "p { text-align:justify; }"
        ]

addDefs = unlines 
	[ "allZipWith :: (a -> b -> Bool) -> [a] -> [b] -> Bool"
	, "allZipWith p [] [] = True"
	, "allZipWith p [] _  = False"
	, "allZipWith p _  [] = False"
	, "allZipWith p (x:xs) (y:ys) = p x y && allZipWith p xs ys"
	, ""
	, "eitherMap :: (a -> b) -> (c -> d) -> Either a c -> Either b d"
	, "eitherMap f1 f2 (Left v)  = Left (f1 v)"
	, "eitherMap f1 f2 (Right v) = Right (f2 v)"
	, ""
	, "andEither :: (a -> b -> Bool) -> (c -> d -> Bool) -> Either a c -> Bool"
	, "andEither p1 p2 (Left v1)  (Left v2)  = p1 v1 v2"
	, "andEither p1 p2 (Right v1) (Right v2) = p2 v1 v2"
	, "andEither _  _  _          _          = False"
	]
