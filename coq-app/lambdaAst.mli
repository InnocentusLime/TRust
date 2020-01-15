type token =
  | EOF
  | COMMA
  | ARROW
  | IDENT of (string)
  | COLLON
  | LPARAN
  | RPARAN
  | SLASH
  | FORALL
  | DOT
  | KIND_TYPE
  | KIND_SET
  | KIND_PROP
  | APP
  | ABS
  | TOP_QUIT
  | TOP_AXIOM
  | TOP_CHECK
  | TOP_INFER
  | TOP_DELETE
  | TOP_LIST

val top_level_command :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Core.ast
