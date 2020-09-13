type token =
  | TRUTH
  | FALSITY
  | INT of (string)
  | IDENT of (string)
  | SPECIAL_IDENT of (string)
  | COMMENT of (string)
  | FN_PTR of (string)
  | LET
  | EQ
  | PLUS
  | MINUS
  | MULTIPLY
  | DIVIDE
  | UMINUS
  | LANGLE
  | RANGLE
  | LANGLE_EQ
  | RANGLE_EQ
  | LONG_EQ
  | NEWLINE
  | EOF
  | SEMICOLLON
  | LPARAN
  | RPARAN
  | LBRACE
  | RBRACE
  | LSQBR
  | RSQBR
  | IF
  | ELSE
  | FN
  | ARROW
  | COMMA
  | CALL
  | INT_T
  | COLLON
  | TYPE_HINT
  | AT
  | PROPAND
  | PROPOR
  | PROP_IMPLICATION
  | PROPEQ
  | FATARROW
  | TOTAL
  | DIVERGENT
  | MAX_COMP_KIND
  | STRING of (string)
  | FORALL
  | SLASH
  | DOT
  | PROPOSITION
  | TYPE
  | PRE_TYPE
  | KIND
  | COMPUTATION_KIND
  | PREDICATE
  | QUIT
  | RESET
  | AXIOM
  | TC_IR_TERM
  | IR_DEFINITION
  | IR_PRINT_DEFINITION
  | REC
  | AND_INTRO
  | OR_INTRO_L
  | OR_INTRO_R
  | AND_ELIM_L
  | AND_ELIM_R
  | OR_ELIM
  | EQ_INTRO
  | EQ_ELIM
  | FALSE_ELIM_PROP
  | FALSE_ELIM_TYPE
  | FN_PTR_TYPE
  | DEREF_FN_PTR
  | PROOF_OF_TRUTH

val rust_file :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> RustTerm.item list
val expression :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> RustTerm.expr
val ir_term :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> IrTerm.term
val toplevel_command :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> TopCmd.command
val maybe_toplevel_command :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> TopCmd.command option
