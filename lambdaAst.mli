type token =
  | LEMMA
  | WILDCARD
  | EOF
  | COMMA
  | SEMICOLLON
  | INT of (int)
  | ARROW
  | VAR of (string)
  | COLLON
  | LBRACE
  | RBRACE
  | LPARAN
  | RPARAN
  | ZERO
  | SUCC
  | NIL
  | TRUE
  | FALSE
  | SLASH
  | FORALL
  | EXISTS
  | EQ
  | PROP_AND
  | PROP_OR
  | PROP_IMPLIES
  | TOP
  | BOT
  | DOT
  | TYPE_HINT
  | UNIT
  | BOOL
  | NAT
  | BAR
  | LSQ
  | RSQ
  | PROD
  | LANGLE
  | RANGLE
  | SUBTYPE
  | PROP
  | SMALL
  | TYPE
  | NATREC
  | BOOLREC
  | SUMBOOLREC
  | CONVERT
  | EXTRACT
  | MEMBERSHIP
  | SUBTRANS
  | SUBPROD
  | SUBREFL
  | SUBSUB
  | SUBGEN
  | SUBUNREFINE
  | AMPERSAND
  | SBOOLL
  | SBOOLR
  | OR_INTROL
  | OR_INTROR
  | AND_INTRO
  | EQ_REFL
  | EXIST
  | APP
  | ABS

val lambda_term :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> PreIr.term_ast
