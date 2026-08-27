-- | The lexical facts of the language, shared by the megaparsec parser
-- ("Telomare.Parse") and the error-tolerant LSP lexer, so the two cannot
-- drift. This module must stay free of parser machinery.
module Telomare.Lexical where

import Data.Char (isAlphaNum, isLetter)

reservedWords :: [String]
reservedWords = ["let", "in", "if", "then", "else", "case", "of", "import", "qualified", "as"]

identifierStart :: Char -> Bool
identifierStart = isLetter

identifierContinueChar :: Char -> Bool
identifierContinueChar c = isAlphaNum c || c == '_' || c == '.'

lineCommentStart :: String
lineCommentStart = "--"

blockCommentDelims :: (String, String)
blockCommentDelims = ("{-", "-}")
