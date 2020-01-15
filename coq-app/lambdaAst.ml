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

open Parsing;;
let _ = parse_error;;
let yytransl_const = [|
    0 (* EOF *);
  257 (* COMMA *);
  258 (* ARROW *);
  260 (* COLLON *);
  261 (* LPARAN *);
  262 (* RPARAN *);
  263 (* SLASH *);
  264 (* FORALL *);
  265 (* DOT *);
  266 (* KIND_TYPE *);
  267 (* KIND_SET *);
  268 (* KIND_PROP *);
  269 (* APP *);
  270 (* ABS *);
  272 (* TOP_QUIT *);
  273 (* TOP_AXIOM *);
  274 (* TOP_CHECK *);
  275 (* TOP_INFER *);
  276 (* TOP_DELETE *);
  277 (* TOP_LIST *);
    0|]

let yytransl_block = [|
  259 (* IDENT *);
    0|]

let yylhs = "\255\255\
\002\000\002\000\002\000\002\000\003\000\003\000\003\000\003\000\
\004\000\004\000\005\000\005\000\006\000\006\000\006\000\006\000\
\006\000\006\000\001\000\000\000"

let yylen = "\002\000\
\001\000\001\000\001\000\001\000\003\000\001\000\006\000\006\000\
\001\000\003\000\001\000\002\000\001\000\003\000\001\000\003\000\
\002\000\001\000\003\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\013\000\000\000\000\000\000\000\015\000\018\000\
\020\000\000\000\000\000\004\000\000\000\001\000\002\000\003\000\
\009\000\000\000\017\000\000\000\014\000\000\000\000\000\000\000\
\000\000\000\000\016\000\019\000\000\000\000\000\010\000\000\000\
\012\000\000\000\000\000\005\000\000\000\000\000\000\000\000\000\
\007\000\008\000"

let yydgoto = "\002\000\
\009\000\017\000\024\000\025\000\026\000\010\000"

let yysindex = "\001\000\
\022\255\000\000\000\000\001\255\023\255\023\255\000\000\000\000\
\000\000\006\255\023\255\000\000\000\255\000\000\000\000\000\000\
\000\000\023\255\000\000\009\000\000\000\017\255\024\255\038\255\
\028\255\023\255\000\000\000\000\041\255\042\255\000\000\000\255\
\000\000\000\255\000\255\000\000\039\255\040\255\000\255\000\255\
\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\013\255\008\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000"

let yygindex = "\000\000\
\000\000\000\000\253\255\251\255\000\000\000\000"

let yytablesize = 49
let yytable = "\018\000\
\019\000\001\000\012\000\011\000\013\000\021\000\022\000\023\000\
\028\000\014\000\015\000\016\000\027\000\006\000\020\000\011\000\
\006\000\011\000\011\000\029\000\033\000\011\000\011\000\011\000\
\011\000\012\000\030\000\013\000\036\000\032\000\037\000\038\000\
\014\000\015\000\016\000\041\000\042\000\003\000\004\000\005\000\
\006\000\007\000\008\000\031\000\034\000\035\000\000\000\039\000\
\040\000"

let yycheck = "\005\000\
\006\000\001\000\003\001\003\001\005\001\011\000\007\001\008\001\
\000\000\010\001\011\001\012\001\018\000\006\001\009\001\003\001\
\009\001\005\001\006\001\003\001\026\000\009\001\010\001\011\001\
\012\001\003\001\003\001\005\001\032\000\002\001\034\000\035\000\
\010\001\011\001\012\001\039\000\040\000\016\001\017\001\018\001\
\019\001\020\001\021\001\006\001\004\001\004\001\255\255\009\001\
\009\001"

let yynames_const = "\
  EOF\000\
  COMMA\000\
  ARROW\000\
  COLLON\000\
  LPARAN\000\
  RPARAN\000\
  SLASH\000\
  FORALL\000\
  DOT\000\
  KIND_TYPE\000\
  KIND_SET\000\
  KIND_PROP\000\
  APP\000\
  ABS\000\
  TOP_QUIT\000\
  TOP_AXIOM\000\
  TOP_CHECK\000\
  TOP_INFER\000\
  TOP_DELETE\000\
  TOP_LIST\000\
  "

let yynames_block = "\
  IDENT\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    Obj.repr(
# 42 "LambdaAst.mly"
            ( Core.SRT Core.Kind )
# 146 "LambdaAst.ml"
               : 'const))
; (fun __caml_parser_env ->
    Obj.repr(
# 43 "LambdaAst.mly"
           ( Core.SRT Core.Set )
# 152 "LambdaAst.ml"
               : 'const))
; (fun __caml_parser_env ->
    Obj.repr(
# 44 "LambdaAst.mly"
            ( Core.SRT Core.Prop )
# 158 "LambdaAst.ml"
               : 'const))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 45 "LambdaAst.mly"
        ( Core.REF _1 )
# 165 "LambdaAst.ml"
               : 'const))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'atom_term) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 47 "LambdaAst.mly"
                       ( Core.PROD ("_", _1, _3) )
# 173 "LambdaAst.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'app_term) in
    Obj.repr(
# 48 "LambdaAst.mly"
                     ( _1 )
# 180 "LambdaAst.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 49 "LambdaAst.mly"
                                             ( Core.ABS (_2, _4, _6) )
# 189 "LambdaAst.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 50 "LambdaAst.mly"
                                    ( Core.PROD (_2, _4, _6) )
# 198 "LambdaAst.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'const) in
    Obj.repr(
# 52 "LambdaAst.mly"
        ( _1 )
# 205 "LambdaAst.ml"
               : 'atom_term))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 53 "LambdaAst.mly"
                     ( _2 )
# 212 "LambdaAst.ml"
               : 'atom_term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'atom_term) in
    Obj.repr(
# 55 "LambdaAst.mly"
            ( _1 )
# 219 "LambdaAst.ml"
               : 'app_term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'app_term) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'atom_term) in
    Obj.repr(
# 56 "LambdaAst.mly"
                     ( Core.APP (_1, _2) )
# 227 "LambdaAst.ml"
               : 'app_term))
; (fun __caml_parser_env ->
    Obj.repr(
# 58 "LambdaAst.mly"
           ( Core.AST_QUIT )
# 233 "LambdaAst.ml"
               : 'command))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'atom_term) in
    Obj.repr(
# 59 "LambdaAst.mly"
                            ( Core.AST_AXIOM (_2, _3) )
# 241 "LambdaAst.ml"
               : 'command))
; (fun __caml_parser_env ->
    Obj.repr(
# 60 "LambdaAst.mly"
             ( Core.AST_DELETE )
# 247 "LambdaAst.ml"
               : 'command))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'atom_term) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'atom_term) in
    Obj.repr(
# 61 "LambdaAst.mly"
                                ( Core.AST_CHECK (_2, _3) )
# 255 "LambdaAst.ml"
               : 'command))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'atom_term) in
    Obj.repr(
# 62 "LambdaAst.mly"
                      ( Core.AST_INFER _2 )
# 262 "LambdaAst.ml"
               : 'command))
; (fun __caml_parser_env ->
    Obj.repr(
# 63 "LambdaAst.mly"
           ( Core.AST_LIST )
# 268 "LambdaAst.ml"
               : 'command))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'command) in
    Obj.repr(
# 65 "LambdaAst.mly"
                  ( _1 )
# 275 "LambdaAst.ml"
               : Core.ast))
(* Entry top_level_command *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let top_level_command (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Core.ast)
