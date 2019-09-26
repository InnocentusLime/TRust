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

open Parsing;;
let _ = parse_error;;
# 2 "lambdaAst.mly"
open PreIr;;
# 53 "lambdaAst.ml"
let yytransl_const = [|
    0 (* EOF *);
  257 (* COMMA *);
  259 (* ARROW *);
  261 (* COLLON *);
  262 (* LBRACE *);
  263 (* RBRACE *);
  264 (* LPARAN *);
  265 (* RPARAN *);
  266 (* ZERO *);
  267 (* SUCC *);
  268 (* NIL *);
  269 (* TRUE *);
  270 (* FALSE *);
  271 (* FOR *);
  272 (* IF *);
  273 (* THEN *);
  274 (* ELSE *);
  275 (* DO *);
  276 (* SLASH *);
  277 (* FORALL *);
  278 (* EXISTS *);
  279 (* EQ *);
  280 (* PROP_AND *);
  281 (* PROP_OR *);
  282 (* PROP_IMPLIES *);
  283 (* TOP *);
  284 (* BOT *);
  285 (* DOT *);
  286 (* TYPE_HINT *);
  287 (* UNIT *);
  288 (* BOOL *);
  289 (* NAT *);
  290 (* FAT_ARROW *);
  291 (* GENERIC_TYPE *);
  292 (* ARROW_TYPE *);
  293 (* REFINED_TYPE *);
  294 (* BAR *);
  295 (* LSQ *);
  296 (* RSQ *);
  297 (* APP *);
  298 (* PROD *);
  299 (* LANGLE *);
  300 (* RANGLE *);
    0|]

let yytransl_block = [|
  258 (* INT *);
  260 (* VAR *);
    0|]

let yylhs = "\255\255\
\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\
\002\000\002\000\005\000\005\000\005\000\005\000\005\000\004\000\
\004\000\004\000\004\000\004\000\004\000\006\000\006\000\003\000\
\003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
\003\000\003\000\003\000\003\000\003\000\003\000\003\000\007\000\
\007\000\007\000\007\000\008\000\008\000\008\000\008\000\001\000\
\000\000"

let yylen = "\002\000\
\001\000\001\000\003\000\003\000\003\000\003\000\005\000\006\000\
\006\000\004\000\001\000\001\000\001\000\001\000\003\000\001\000\
\003\000\007\000\004\000\007\000\001\000\003\000\003\000\001\000\
\001\000\001\000\001\000\001\000\003\000\008\000\008\000\007\000\
\007\000\003\000\003\000\013\000\012\000\010\000\009\000\002\000\
\002\000\004\000\004\000\001\000\001\000\003\000\003\000\002\000\
\002\000"

let yydefred = "\000\000\
\000\000\000\000\028\000\000\000\024\000\025\000\027\000\026\000\
\000\000\000\000\000\000\049\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\048\000\000\000\000\000\
\000\000\000\000\000\000\000\000\029\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\035\000\034\000\000\000\000\000\
\000\000\000\000\000\000\000\000\012\000\011\000\013\000\000\000\
\000\000\021\000\000\000\000\000\000\000\000\000\000\000\001\000\
\002\000\000\000\000\000\000\000\000\000\047\000\046\000\014\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\043\000\000\000\042\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\015\000\000\000\017\000\
\000\000\000\000\023\000\000\000\003\000\000\000\000\000\000\000\
\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\033\000\032\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\031\000\030\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\039\000\000\000\000\000\000\000\000\000\
\000\000\020\000\018\000\000\000\038\000\000\000\000\000\000\000\
\037\000\000\000\036\000"

let yydgoto = "\002\000\
\012\000\058\000\059\000\070\000\049\000\050\000\016\000\021\000"

let yysindex = "\010\000\
\206\000\000\000\000\000\126\000\000\000\000\000\000\000\000\000\
\206\000\206\000\206\000\000\000\001\000\020\255\139\000\166\000\
\211\255\097\255\206\255\228\255\239\254\000\000\034\255\021\255\
\056\255\242\255\043\255\242\255\000\000\043\255\094\255\054\000\
\098\255\054\000\206\000\206\000\000\000\000\000\192\000\079\255\
\000\000\111\255\018\000\153\255\000\000\000\000\000\000\060\255\
\130\255\000\000\089\255\206\000\032\000\172\255\183\255\000\000\
\000\000\235\255\076\255\206\000\053\000\000\000\000\000\000\000\
\222\000\255\254\206\000\190\255\195\255\209\255\205\255\192\000\
\000\000\012\255\000\000\102\255\181\255\075\000\027\255\232\255\
\054\000\054\000\054\000\230\255\206\000\112\255\249\255\195\255\
\206\000\092\000\179\000\192\000\192\000\000\000\192\000\000\000\
\192\000\130\255\000\000\241\255\000\000\192\000\054\000\192\000\
\000\000\244\255\253\254\008\000\113\255\253\255\014\000\109\000\
\193\000\000\000\000\000\009\255\222\255\013\000\206\000\038\255\
\253\254\062\255\206\000\192\000\015\000\206\000\000\000\000\000\
\054\000\024\000\117\255\054\000\054\000\121\255\013\000\206\000\
\145\255\114\255\192\000\000\000\253\254\253\254\029\000\146\255\
\019\000\000\000\000\000\206\000\000\000\035\000\164\255\206\000\
\000\000\204\255\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\016\000\021\000\000\000\000\000\000\000\000\000\
\000\000\000\000\169\255\000\000\000\000\188\255\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\152\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\072\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\152\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\004\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\120\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\069\255\086\255\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\024\255\000\000\000\000\
\125\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\030\255\000\000\
\000\000\000\000\000\000\000\000\179\255\217\255\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\004\000\255\255\234\255\226\000\237\000\250\255\229\000"

let yytablesize = 511
let yytable = "\013\000\
\022\000\072\000\015\000\048\000\020\000\051\000\014\000\017\000\
\018\000\019\000\001\000\072\000\014\000\027\000\030\000\064\000\
\066\000\027\000\030\000\097\000\081\000\082\000\037\000\024\000\
\015\000\039\000\015\000\089\000\020\000\020\000\019\000\102\000\
\019\000\019\000\019\000\038\000\007\000\061\000\007\000\025\000\
\072\000\015\000\045\000\046\000\047\000\014\000\129\000\019\000\
\019\000\096\000\076\000\078\000\019\000\007\000\007\000\103\000\
\077\000\019\000\086\000\040\000\091\000\019\000\072\000\007\000\
\072\000\090\000\132\000\019\000\073\000\116\000\117\000\023\000\
\118\000\007\000\016\000\005\000\027\000\005\000\016\000\120\000\
\016\000\122\000\113\000\109\000\105\000\106\000\107\000\112\000\
\027\000\030\000\133\000\072\000\006\000\005\000\006\000\016\000\
\016\000\075\000\085\000\052\000\016\000\135\000\005\000\060\000\
\023\000\016\000\121\000\067\000\100\000\016\000\027\000\030\000\
\005\000\033\000\068\000\016\000\147\000\131\000\110\000\006\000\
\146\000\134\000\022\000\140\000\137\000\023\000\022\000\143\000\
\022\000\006\000\023\000\010\000\138\000\010\000\144\000\141\000\
\142\000\081\000\082\000\034\000\023\000\023\000\124\000\022\000\
\022\000\023\000\151\000\083\000\022\000\023\000\154\000\145\000\
\149\000\022\000\014\000\028\000\071\000\022\000\010\000\028\000\
\014\000\028\000\028\000\022\000\028\000\028\000\028\000\028\000\
\010\000\040\000\153\000\074\000\040\000\023\000\023\000\079\000\
\040\000\040\000\040\000\040\000\028\000\040\000\040\000\040\000\
\040\000\008\000\080\000\008\000\041\000\101\000\028\000\041\000\
\023\000\014\000\092\000\041\000\041\000\041\000\041\000\093\000\
\041\000\041\000\041\000\041\000\081\000\082\000\035\000\040\000\
\040\000\003\000\155\000\072\000\008\000\026\000\083\000\005\000\
\006\000\094\000\007\000\008\000\009\000\010\000\008\000\009\000\
\072\000\009\000\041\000\041\000\036\000\031\000\130\000\003\000\
\023\000\095\000\023\000\028\000\104\000\005\000\006\000\023\000\
\007\000\008\000\009\000\010\000\011\000\041\000\119\000\042\000\
\108\000\043\000\009\000\005\000\006\000\032\000\007\000\008\000\
\009\000\010\000\081\000\082\000\009\000\014\000\044\000\062\000\
\063\000\111\000\011\000\081\000\083\000\123\000\125\000\072\000\
\045\000\046\000\047\000\126\000\136\000\069\000\084\000\042\000\
\011\000\043\000\139\000\005\000\006\000\023\000\007\000\008\000\
\009\000\010\000\148\000\003\000\150\000\014\000\044\000\053\000\
\152\000\005\000\006\000\098\000\007\000\008\000\009\000\010\000\
\045\000\046\000\047\000\014\000\054\000\055\000\099\000\045\000\
\011\000\003\000\056\000\057\000\044\000\053\000\000\000\005\000\
\006\000\000\000\007\000\008\000\009\000\010\000\011\000\000\000\
\000\000\000\000\054\000\055\000\081\000\082\000\003\000\000\000\
\056\000\057\000\026\000\000\000\005\000\006\000\083\000\007\000\
\008\000\009\000\010\000\000\000\011\000\000\000\000\000\003\000\
\087\000\085\000\000\000\026\000\114\000\005\000\006\000\023\000\
\007\000\008\000\009\000\010\000\000\000\000\000\000\000\000\000\
\003\000\011\000\000\000\000\000\026\000\127\000\005\000\006\000\
\023\000\007\000\008\000\009\000\010\000\000\000\000\000\000\000\
\000\000\003\000\011\000\000\000\000\000\004\000\000\000\005\000\
\006\000\023\000\007\000\008\000\009\000\010\000\003\000\000\000\
\000\000\014\000\026\000\011\000\005\000\006\000\000\000\007\000\
\008\000\009\000\010\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\011\000\000\000\000\000\023\000\
\000\000\003\000\000\000\000\000\000\000\028\000\029\000\005\000\
\006\000\011\000\007\000\008\000\009\000\010\000\003\000\000\000\
\000\000\000\000\028\000\115\000\005\000\006\000\000\000\007\000\
\008\000\009\000\010\000\064\000\003\000\042\000\000\000\065\000\
\028\000\128\000\005\000\006\000\011\000\007\000\008\000\009\000\
\010\000\003\000\000\000\000\000\044\000\004\000\000\000\005\000\
\006\000\011\000\007\000\008\000\009\000\010\000\045\000\046\000\
\047\000\088\000\000\000\042\000\000\000\065\000\000\000\011\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\044\000\000\000\011\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\045\000\046\000\047\000"

let yycheck = "\001\000\
\000\000\003\001\004\000\026\000\011\000\028\000\003\001\009\000\
\010\000\011\000\001\000\003\001\009\001\015\000\016\000\004\001\
\039\000\019\000\020\000\008\001\024\001\025\001\040\001\004\001\
\026\000\005\001\028\000\029\001\035\000\036\000\007\001\005\001\
\009\001\035\000\036\000\002\001\007\001\034\000\009\001\020\001\
\003\001\043\000\031\001\032\001\033\001\042\001\038\001\024\001\
\025\001\072\000\052\000\053\000\029\001\024\001\025\001\029\001\
\053\000\034\001\060\000\004\001\067\000\038\001\003\001\034\001\
\003\001\067\000\029\001\044\001\009\001\092\000\093\000\029\001\
\095\000\044\001\003\001\007\001\078\000\009\001\007\001\102\000\
\009\001\104\000\089\000\085\000\081\000\082\000\083\000\089\000\
\090\000\091\000\029\001\003\001\007\001\025\001\009\001\024\001\
\025\001\009\001\023\001\006\001\029\001\124\000\034\001\006\001\
\029\001\034\001\103\000\029\001\007\001\038\001\112\000\113\000\
\044\001\017\001\004\001\044\001\139\000\119\000\007\001\034\001\
\007\001\123\000\003\001\007\001\126\000\029\001\007\001\007\001\
\009\001\044\001\029\001\007\001\129\000\009\001\136\000\132\000\
\133\000\024\001\025\001\043\001\029\001\029\001\030\001\024\001\
\025\001\029\001\148\000\034\001\029\001\029\001\152\000\007\001\
\007\001\034\001\003\001\004\001\004\001\038\001\034\001\008\001\
\009\001\010\001\011\001\044\001\013\001\014\001\015\001\016\001\
\044\001\001\001\007\001\042\001\004\001\029\001\029\001\004\001\
\008\001\009\001\010\001\011\001\029\001\013\001\014\001\015\001\
\016\001\007\001\004\001\009\001\001\001\009\001\039\001\004\001\
\029\001\042\001\005\001\008\001\009\001\010\001\011\001\005\001\
\013\001\014\001\015\001\016\001\024\001\025\001\001\001\039\001\
\040\001\004\001\007\001\003\001\034\001\008\001\034\001\010\001\
\011\001\009\001\013\001\014\001\015\001\016\001\044\001\007\001\
\003\001\009\001\039\001\040\001\001\001\019\001\009\001\004\001\
\029\001\029\001\029\001\008\001\005\001\010\001\011\001\029\001\
\013\001\014\001\015\001\016\001\039\001\004\001\006\001\006\001\
\019\001\008\001\034\001\010\001\011\001\043\001\013\001\014\001\
\015\001\016\001\024\001\025\001\044\001\020\001\021\001\035\000\
\036\000\017\001\039\001\024\001\034\001\006\001\018\001\003\001\
\031\001\032\001\033\001\006\001\006\001\004\001\044\001\006\001\
\039\001\008\001\003\001\010\001\011\001\029\001\013\001\014\001\
\015\001\016\001\006\001\004\001\018\001\020\001\021\001\008\001\
\006\001\010\001\011\001\074\000\013\001\014\001\015\001\016\001\
\031\001\032\001\033\001\020\001\021\001\022\001\074\000\040\001\
\039\001\004\001\027\001\028\001\040\001\008\001\255\255\010\001\
\011\001\255\255\013\001\014\001\015\001\016\001\039\001\255\255\
\255\255\255\255\021\001\022\001\024\001\025\001\004\001\255\255\
\027\001\028\001\008\001\255\255\010\001\011\001\034\001\013\001\
\014\001\015\001\016\001\255\255\039\001\255\255\255\255\004\001\
\044\001\023\001\255\255\008\001\009\001\010\001\011\001\029\001\
\013\001\014\001\015\001\016\001\255\255\255\255\255\255\255\255\
\004\001\039\001\255\255\255\255\008\001\009\001\010\001\011\001\
\029\001\013\001\014\001\015\001\016\001\255\255\255\255\255\255\
\255\255\004\001\039\001\255\255\255\255\008\001\255\255\010\001\
\011\001\029\001\013\001\014\001\015\001\016\001\004\001\255\255\
\255\255\020\001\008\001\039\001\010\001\011\001\255\255\013\001\
\014\001\015\001\016\001\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\039\001\255\255\255\255\029\001\
\255\255\004\001\255\255\255\255\255\255\008\001\009\001\010\001\
\011\001\039\001\013\001\014\001\015\001\016\001\004\001\255\255\
\255\255\255\255\008\001\009\001\010\001\011\001\255\255\013\001\
\014\001\015\001\016\001\004\001\004\001\006\001\255\255\008\001\
\008\001\009\001\010\001\011\001\039\001\013\001\014\001\015\001\
\016\001\004\001\255\255\255\255\021\001\008\001\255\255\010\001\
\011\001\039\001\013\001\014\001\015\001\016\001\031\001\032\001\
\033\001\004\001\255\255\006\001\255\255\008\001\255\255\039\001\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\021\001\255\255\039\001\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\031\001\032\001\033\001"

let yynames_const = "\
  EOF\000\
  COMMA\000\
  ARROW\000\
  COLLON\000\
  LBRACE\000\
  RBRACE\000\
  LPARAN\000\
  RPARAN\000\
  ZERO\000\
  SUCC\000\
  NIL\000\
  TRUE\000\
  FALSE\000\
  FOR\000\
  IF\000\
  THEN\000\
  ELSE\000\
  DO\000\
  SLASH\000\
  FORALL\000\
  EXISTS\000\
  EQ\000\
  PROP_AND\000\
  PROP_OR\000\
  PROP_IMPLIES\000\
  TOP\000\
  BOT\000\
  DOT\000\
  TYPE_HINT\000\
  UNIT\000\
  BOOL\000\
  NAT\000\
  FAT_ARROW\000\
  GENERIC_TYPE\000\
  ARROW_TYPE\000\
  REFINED_TYPE\000\
  BAR\000\
  LSQ\000\
  RSQ\000\
  APP\000\
  PROD\000\
  LANGLE\000\
  RANGLE\000\
  "

let yynames_block = "\
  INT\000\
  VAR\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    Obj.repr(
# 50 "lambdaAst.mly"
      ( Top )
# 385 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    Obj.repr(
# 51 "lambdaAst.mly"
      ( Bot )
# 391 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'prop_grammar) in
    Obj.repr(
# 52 "lambdaAst.mly"
                             ( _2 )
# 398 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'prop_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'prop_grammar) in
    Obj.repr(
# 53 "lambdaAst.mly"
                                     ( Conjunction (_1, _3) )
# 406 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'prop_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'prop_grammar) in
    Obj.repr(
# 54 "lambdaAst.mly"
                                    ( Disjunction (_1, _3) )
# 414 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'prop_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'prop_grammar) in
    Obj.repr(
# 55 "lambdaAst.mly"
                                                         ( Implication (_1, _3) )
# 422 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : 'term_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'term_grammar) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'type_grammar) in
    Obj.repr(
# 56 "lambdaAst.mly"
                                                      ( Eq (_1, _3, _5) )
# 431 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'type_grammar) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'prop_grammar) in
    Obj.repr(
# 57 "lambdaAst.mly"
                                                                     ( Forall (_2, _4, _6) )
# 440 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'type_grammar) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'prop_grammar) in
    Obj.repr(
# 58 "lambdaAst.mly"
                                                                     ( Exists (_2, _4, _6) )
# 449 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'prop_grammar) in
    Obj.repr(
# 59 "lambdaAst.mly"
                                                 ( ForallGen (_2, _4) )
# 457 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    Obj.repr(
# 61 "lambdaAst.mly"
       ( Bool )
# 463 "lambdaAst.ml"
               : 'atom_type_grammar))
; (fun __caml_parser_env ->
    Obj.repr(
# 62 "lambdaAst.mly"
       ( Unit )
# 469 "lambdaAst.ml"
               : 'atom_type_grammar))
; (fun __caml_parser_env ->
    Obj.repr(
# 63 "lambdaAst.mly"
      ( Nat )
# 475 "lambdaAst.ml"
               : 'atom_type_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 64 "lambdaAst.mly"
      ( TVar _1 )
# 482 "lambdaAst.ml"
               : 'atom_type_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'type_grammar) in
    Obj.repr(
# 65 "lambdaAst.mly"
                             ( _2 )
# 489 "lambdaAst.ml"
               : 'atom_type_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'atom_type_grammar) in
    Obj.repr(
# 67 "lambdaAst.mly"
                    ( _1 )
# 496 "lambdaAst.ml"
               : 'type_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'type_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'type_grammar) in
    Obj.repr(
# 68 "lambdaAst.mly"
                                                   ( Map ("_", _1, _3) )
# 504 "lambdaAst.ml"
               : 'type_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : 'type_grammar) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'type_grammar) in
    Obj.repr(
# 69 "lambdaAst.mly"
                                                                          ( Map (_2, _4, _7) )
# 513 "lambdaAst.ml"
               : 'type_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'type_grammar) in
    Obj.repr(
# 70 "lambdaAst.mly"
                                                 ( Gen (_2, _4) )
# 521 "lambdaAst.ml"
               : 'type_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : 'type_grammar) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'prop_grammar) in
    Obj.repr(
# 71 "lambdaAst.mly"
                                                                            ( Refine (_2, _4, _6) )
# 530 "lambdaAst.ml"
               : 'type_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'prod_type) in
    Obj.repr(
# 72 "lambdaAst.mly"
                       ( Prod _1 )
# 537 "lambdaAst.ml"
               : 'type_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'atom_type_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'atom_type_grammar) in
    Obj.repr(
# 74 "lambdaAst.mly"
                                           ( [_1; _3] )
# 545 "lambdaAst.ml"
               : 'prod_type))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'atom_type_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'prod_type) in
    Obj.repr(
# 75 "lambdaAst.mly"
                                   ( _1 :: _3 )
# 553 "lambdaAst.ml"
               : 'prod_type))
; (fun __caml_parser_env ->
    Obj.repr(
# 77 "lambdaAst.mly"
       ( NatO )
# 559 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    Obj.repr(
# 78 "lambdaAst.mly"
       ( NatSucc )
# 565 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    Obj.repr(
# 79 "lambdaAst.mly"
        ( False )
# 571 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    Obj.repr(
# 80 "lambdaAst.mly"
       ( True )
# 577 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 81 "lambdaAst.mly"
      ( Var _1 )
# 584 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'app_term_grammar) in
    Obj.repr(
# 82 "lambdaAst.mly"
                                 ( _2 )
# 591 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 3 : 'type_grammar) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'app_term_grammar) in
    Obj.repr(
# 83 "lambdaAst.mly"
                                                                   ( Abs (_3, _5, _7) )
# 600 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 3 : 'type_grammar) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'term_grammar) in
    Obj.repr(
# 84 "lambdaAst.mly"
                                                               ( Abs (_3, _5, _7) )
# 609 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _4 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'app_term_grammar) in
    Obj.repr(
# 85 "lambdaAst.mly"
                                                     ( Generic (_4, _6) )
# 617 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _4 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'term_grammar) in
    Obj.repr(
# 86 "lambdaAst.mly"
                                                 ( Generic (_4, _6) )
# 625 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'term_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 87 "lambdaAst.mly"
                       ( Proj (_1, _3) )
# 633 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'term_list) in
    Obj.repr(
# 88 "lambdaAst.mly"
                    ( Tuple _2 )
# 640 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 11 : 'term_grammar) in
    let _4 = (Parsing.peek_val __caml_parser_env 9 : 'prop_grammar) in
    let _8 = (Parsing.peek_val __caml_parser_env 5 : 'term_grammar) in
    let _12 = (Parsing.peek_val __caml_parser_env 1 : 'term_grammar) in
    Obj.repr(
# 89 "lambdaAst.mly"
                                                                                                             ( Ite (_2, _8, _12, _4) )
# 650 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 10 : 'term_grammar) in
    let _4 = (Parsing.peek_val __caml_parser_env 8 : 'prop_grammar) in
    let _8 = (Parsing.peek_val __caml_parser_env 4 : 'term_grammar) in
    let _11 = (Parsing.peek_val __caml_parser_env 1 : 'term_grammar) in
    Obj.repr(
# 90 "lambdaAst.mly"
                                                                                                       ( For (_2, _8, _11, _4) )
# 660 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 8 : 'term_grammar) in
    let _5 = (Parsing.peek_val __caml_parser_env 5 : 'term_grammar) in
    let _9 = (Parsing.peek_val __caml_parser_env 1 : 'term_grammar) in
    Obj.repr(
# 91 "lambdaAst.mly"
                                                                                  ( Ite (_2, _5, _9, Top) )
# 669 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 7 : 'term_grammar) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : 'term_grammar) in
    let _8 = (Parsing.peek_val __caml_parser_env 1 : 'term_grammar) in
    Obj.repr(
# 92 "lambdaAst.mly"
                                                                            ( For (_2, _5, _8, Top) )
# 678 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'term_grammar) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'term_grammar) in
    Obj.repr(
# 94 "lambdaAst.mly"
                                      ( App (_1, _2) )
# 686 "lambdaAst.ml"
               : 'app_term_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'app_term_grammar) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'term_grammar) in
    Obj.repr(
# 95 "lambdaAst.mly"
                                          ( App (_1, _2) )
# 694 "lambdaAst.ml"
               : 'app_term_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'app_term_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'type_grammar) in
    Obj.repr(
# 96 "lambdaAst.mly"
                                                        ( TApp (_1, _3) )
# 702 "lambdaAst.ml"
               : 'app_term_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'term_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'type_grammar) in
    Obj.repr(
# 97 "lambdaAst.mly"
                                                    ( TApp (_1, _3) )
# 710 "lambdaAst.ml"
               : 'app_term_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'app_term_grammar) in
    Obj.repr(
# 99 "lambdaAst.mly"
                   ( [_1] )
# 717 "lambdaAst.ml"
               : 'term_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'term_grammar) in
    Obj.repr(
# 100 "lambdaAst.mly"
               ( [_1] )
# 724 "lambdaAst.ml"
               : 'term_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'app_term_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'term_list) in
    Obj.repr(
# 101 "lambdaAst.mly"
                                   ( _1 :: _3 )
# 732 "lambdaAst.ml"
               : 'term_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'term_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'term_list) in
    Obj.repr(
# 102 "lambdaAst.mly"
                               ( _1 :: _3 )
# 740 "lambdaAst.ml"
               : 'term_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'term_grammar) in
    Obj.repr(
# 104 "lambdaAst.mly"
                   ( _1 )
# 747 "lambdaAst.ml"
               : PreIr.term_ast))
(* Entry lambda_term *)
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
let lambda_term (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : PreIr.term_ast)
