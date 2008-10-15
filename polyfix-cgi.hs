module Main where

import ParseType (parseType')
import SimpleFT  (freeTheorem)
import Expr (specialize)
import ExFindExtended (getComplete')
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

import Network.CGI
import Data.ByteString.Lazy.UTF8 (fromString)
import Text.XHtml
import Control.Monad
import System.Random (randomRIO)
import Data.Maybe
import Text.PrettyPrint.HughesPJ (render)

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
		maindiv ( p << ("© 2008 Daniel Seidel und Joachim Breitner <" +++
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
	pre << show (specialize ft_simple)
	) +++
	maindiv << (
	h3 << "The counter-example" +++
	case counter_example of 
		Left err -> p << "No term could be derived: " +++ pre << err
		Right (res,used) ->
			p << ("By disregarding the strictness conditions for the pointed "+++
                              "variables(?), the following term is a counter example:" +++
                              pre << ("f = " ++ res) ) +++
			p << ("Wheres the abstraced variables are chosen as follows:" +++
                              pre << used)
	)
  where ft_full = let properType = "f :: " ++ case span (/='.') typeStr of
                                       (s,"")  -> s
                                       (_,_:s) -> s
		      (ds,es) = runChecks (parse properType >>= check)
                      [s]     = filterSignatures ds
		  in if null es
                     then case interpret [] BasicSubset s of
			Nothing -> Left "interpret returned nothing"
			Just i  -> Right $ render (prettyTheorem [] (asTheorem i)) ++
			      case unfoldLifts [] i of
				[] -> ""
				ls -> "\n\nWhereas the occuring lifts are defined as:\n\n "++
				      unlines (map (render . prettyUnfoldedLift []) ls)
                     else Left (unlines (map render es))
		    
	ft_simple = freeTheorem typ
        counter_example = getComplete' typ
	
