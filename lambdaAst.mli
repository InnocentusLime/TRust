type token =
  | EOF
  | COMMA
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
  | FOR
  | IF
  | THEN
  | ELSE
  | DO
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
  | FAT_ARROW
  | GENERIC_TYPE
  | ARROW_TYPE
  | REFINED_TYPE
  | BAR
  | LSQ
  | RSQ
  | APP
  | PROD
  | LANGLE
  | RANGLE

val lambda_term :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> PreIr.term_ast
