module Parser (tokenizer) where

import Prelude

import Control.Alt ((<|>))
import Control.Lazy (fix)
import Data.Char.Unicode (isAlpha)
import Expr (Expr(..), Proposition)
import Text.Parsing.Parser (Parser)
import Text.Parsing.Parser.Expr (Assoc(..), Operator(..), buildExprParser)
import Text.Parsing.Parser.String (satisfy, char, oneOf)
import Text.Parsing.Parser.Token (LanguageDef, GenLanguageDef(..), TokenParser, makeTokenParser)

propositional :: LanguageDef
propositional = LanguageDef
  { commentStart: ""
  , commentEnd: ""
  , commentLine: ""
  , nestedComments: false
  , opStart: oneOf []
  , opLetter: oneOf []
  , identStart: satisfy isAlpha
  , identLetter: satisfy isAlpha <|> char '\''
  , reservedNames: []
  , reservedOpNames: ["->", "&&", "||", "!"]
  , caseSensitive: true
}

tokenizer :: TokenParser
tokenizer = makeTokenParser propositional

parens :: forall a. Parser String a -> Parser String a
parens = tokenizer.parens

reservedOp :: String -> Parser String Unit
reservedOp = tokenizer.reservedOp

reserved :: String -> Parser String Unit
reserved = tokenizer.reserved

identifier :: Parser String String
identifier = tokenizer.identifier

atomParser :: Parser String Proposition
atomParser = Atom <$> identifier

term :: Parser String Proposition -> Parser String Proposition
term p = parens p <|> atomParser 

propParser :: Parser String Proposition
propParser = let allExprs p = buildExprParser table (term p)
                 table = [ [ Prefix (reservedOp "!" $> Not) ]
                         , [ Infix (reservedOp "||" $> Or) AssocRight ]
                         , [ Infix (reservedOp "&&" $> And) AssocRight ]
                         , [ Infix (reservedOp "->" $> Implies) AssocRight ]
                         ]
             in fix allExprs