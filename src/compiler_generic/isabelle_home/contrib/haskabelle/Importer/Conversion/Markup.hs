{-  Title:      Pure/PIDE/markup.ML
    Author:     Makarius

Quasi-abstract markup elements.
-}

module Importer.Conversion.Markup where

-- cd src/Pure/PIDE; grep ': T$' markup.ML | rev | cut -d ':' -f 2 | cut -d ' ' -f 1 | rev | while read i ; do echo "       | ${i^^}" ; done
data T = EMPTY
       | LANGUAGE_METHOD
       | LANGUAGE_ATTRIBUTE
       | LANGUAGE_ANTIQUOTATION
       | LANGUAGE_RAIL
       | LANGUAGE_PATH
       | LANGUAGE_MIXFIX
       | BINDING
       | COMPLETION
       | NO_COMPLETION
       | POSITION
       | FBREAK
       | ITEM
       | WORDS
       | HIDDEN
       | TFREE
       | TVAR
       | FREE
       | SKOLEM
       | BOUND
       | VAR
       | NUMERAL
       | LITERAL
       | DELIMITER
       | INNER_STRING
       | INNER_CARTOUCHE
       | INNER_COMMENT
       | TOKEN_RANGE
       | SORTING
       | TYPING
       | CLASS_PARAMETER
       | ML_KEYWORD1
       | ML_KEYWORD2
       | ML_KEYWORD3
       | ML_DELIMITER
       | ML_TVAR
       | ML_NUMERAL
       | ML_CHAR
       | ML_STRING
       | ML_COMMENT
       | SML_STRING
       | SML_COMMENT
       | ML_TYPING
       | ANTIQUOTED
       | ANTIQUOTE
       | PARAGRAPH
       | TEXT_FOLD
       | MARKDOWN_PARAGRAPH
       | COMMAND_KEYWORD
       | STRING
       | ALT_STRING
       | VERBATIM
       | CARTOUCHE
       | COMMENT
       | KEYWORD1
       | KEYWORD2
       | KEYWORD3
       | QUASI_KEYWORD
       | IMPROPER
       | OPERATOR
       | GOAL
       | ACCEPTED
       | FORKED
       | JOINED
       | RUNNING
       | FINISHED
       | FAILED
       | CONSOLIDATED
       | STATUS
       | RESULT
       | WRITELN
       | STATE
       | INFORMATION
       | TRACING
       | WARNING
       | LEGACY
       | ERROR
       | SYSTEM
       | REPORT
       | NO_REPORT
       | INTENSIFY

-- cd src/Pure/PIDE; grep ': T$' markup.ML | rev | cut -d ':' -f 2 | cut -d ' ' -f 1 | rev | while read i ; do echo "  ${i^^} -> \"$i\"" ; done
to_ML x = case x of
  EMPTY -> "empty"
  LANGUAGE_METHOD -> "language_method"
  LANGUAGE_ATTRIBUTE -> "language_attribute"
  LANGUAGE_ANTIQUOTATION -> "language_antiquotation"
  LANGUAGE_RAIL -> "language_rail"
  LANGUAGE_PATH -> "language_path"
  LANGUAGE_MIXFIX -> "language_mixfix"
  BINDING -> "binding"
  COMPLETION -> "completion"
  NO_COMPLETION -> "no_completion"
  POSITION -> "position"
  FBREAK -> "fbreak"
  ITEM -> "item"
  WORDS -> "words"
  HIDDEN -> "hidden"
  TFREE -> "tfree"
  TVAR -> "tvar"
  FREE -> "free"
  SKOLEM -> "skolem"
  BOUND -> "bound"
  VAR -> "var"
  NUMERAL -> "numeral"
  LITERAL -> "literal"
  DELIMITER -> "delimiter"
  INNER_STRING -> "inner_string"
  INNER_CARTOUCHE -> "inner_cartouche"
  INNER_COMMENT -> "inner_comment"
  TOKEN_RANGE -> "token_range"
  SORTING -> "sorting"
  TYPING -> "typing"
  CLASS_PARAMETER -> "class_parameter"
  ML_KEYWORD1 -> "ML_keyword1"
  ML_KEYWORD2 -> "ML_keyword2"
  ML_KEYWORD3 -> "ML_keyword3"
  ML_DELIMITER -> "ML_delimiter"
  ML_TVAR -> "ML_tvar"
  ML_NUMERAL -> "ML_numeral"
  ML_CHAR -> "ML_char"
  ML_STRING -> "ML_string"
  ML_COMMENT -> "ML_comment"
  SML_STRING -> "SML_string"
  SML_COMMENT -> "SML_comment"
  ML_TYPING -> "ML_typing"
  ANTIQUOTED -> "antiquoted"
  ANTIQUOTE -> "antiquote"
  PARAGRAPH -> "paragraph"
  TEXT_FOLD -> "text_fold"
  MARKDOWN_PARAGRAPH -> "markdown_paragraph"
  COMMAND_KEYWORD -> "command_keyword"
  STRING -> "string"
  ALT_STRING -> "alt_string"
  VERBATIM -> "verbatim"
  CARTOUCHE -> "cartouche"
  COMMENT -> "comment"
  KEYWORD1 -> "keyword1"
  KEYWORD2 -> "keyword2"
  KEYWORD3 -> "keyword3"
  QUASI_KEYWORD -> "quasi_keyword"
  IMPROPER -> "improper"
  OPERATOR -> "operator"
  GOAL -> "goal"
  ACCEPTED -> "accepted"
  FORKED -> "forked"
  JOINED -> "joined"
  RUNNING -> "running"
  FINISHED -> "finished"
  FAILED -> "failed"
  CONSOLIDATED -> "consolidated"
  STATUS -> "status"
  RESULT -> "result"
  WRITELN -> "writeln"
  STATE -> "state"
  INFORMATION -> "information"
  TRACING -> "tracing"
  WARNING -> "warning"
  LEGACY -> "legacy"
  ERROR -> "error"
  SYSTEM -> "system"
  REPORT -> "report"
  NO_REPORT -> "no_report"
  INTENSIFY -> "intensify"
