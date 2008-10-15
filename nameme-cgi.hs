module Main where

import ParseType (parseType')
import SimpleFT  (freeTheorem)
import ExFindExtended (getComplete')

import Network.CGI
import Data.ByteString.Lazy.UTF8 (fromString)
import Text.XHtml
import Control.Monad
import System.Random (randomRIO)
import Data.Maybe

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
		thetitle << "Name Me" +++
		style ! [ thetype "text/css" ] << cdata cssStyle
	       ) +++
	       body ( form ! [method "POST", action "#"] << (
		thediv ! [theclass "top"] << (
			thespan ! [theclass "title"] << "Name Me" +++
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


askTypeForm = maindiv << p << (
	"Please enter a function type, prepended with a list of unpointed " +++
	"type variables and a single dot." +++ br +++
	input ! [name "type", value "a. (a -> b) -> b"] +++ " " +++
	submit "submit" "Generate Free Theorem and counter example"
	)

typeError typeStr err = maindiv << (
	p << ("Please enter a function type, prepended with a list of unpointed " +++
	      "type variables and a single dot.") +++
	p << (input ! [name "type", value typeStr] +++ " " +++
	      submit "submit" "Generate Free Theorem and counter example") +++
	p << ("There was a problem parsing your type: " +++
  	      pre << err )
	)

generateResult typeStr typ = maindiv << (
	"Please enter a function type, prepended with a list of unpointed " +++
	"type variables and a single dot." +++ br +++
	input ! [name "type", value typeStr] +++ " " +++
	submit "submit" "Generate Free Theorem and counter example"
	) +++
	maindiv << (
	h3 << "The Free Theorem" +++
	p << "For your type, the following Free Theorem holds:" +++
	pre << (show (freeTheorem typ))
	) +++
	maindiv << (
	h3 << "The counter-example" +++
	case getComplete' typ of 
		Left err -> p << "No term could be derived: " +++ err
		Right (res,used) ->
			p << ("By disregarding the strictness conditions for the pointed "+++
                              "variables(?), the following term is a counter example:" +++
                              pre << ("f = " ++ res) ) +++
			p << ("Wheres the abstraced variables are chosen as follows:" +++
                              pre << used)
	)

	
