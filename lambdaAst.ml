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

open Parsing;;
let _ = parse_error;;
# 2 "lambdaAst.mly"
open PreIr;;
# 65 "lambdaAst.ml"
let yytransl_const = [|
  257 (* LEMMA *);
  258 (* WILDCARD *);
    0 (* EOF *);
  259 (* COMMA *);
  260 (* SEMICOLLON *);
  262 (* ARROW *);
  264 (* COLLON *);
  265 (* LBRACE *);
  266 (* RBRACE *);
  267 (* LPARAN *);
  268 (* RPARAN *);
  269 (* ZERO *);
  270 (* SUCC *);
  271 (* NIL *);
  272 (* TRUE *);
  273 (* FALSE *);
  274 (* SLASH *);
  275 (* FORALL *);
  276 (* EXISTS *);
  277 (* EQ *);
  278 (* PROP_AND *);
  279 (* PROP_OR *);
  280 (* PROP_IMPLIES *);
  281 (* TOP *);
  282 (* BOT *);
  283 (* DOT *);
  284 (* TYPE_HINT *);
  285 (* UNIT *);
  286 (* BOOL *);
  287 (* NAT *);
  288 (* BAR *);
  289 (* LSQ *);
  290 (* RSQ *);
  291 (* PROD *);
  292 (* LANGLE *);
  293 (* RANGLE *);
  294 (* SUBTYPE *);
  295 (* PROP *);
  296 (* SMALL *);
  297 (* TYPE *);
  298 (* NATREC *);
  299 (* BOOLREC *);
  300 (* SUMBOOLREC *);
  301 (* CONVERT *);
  302 (* EXTRACT *);
  303 (* MEMBERSHIP *);
  304 (* SUBTRANS *);
  305 (* SUBPROD *);
  306 (* SUBREFL *);
  307 (* SUBSUB *);
  308 (* SUBGEN *);
  309 (* SUBUNREFINE *);
  310 (* AMPERSAND *);
  311 (* SBOOLL *);
  312 (* SBOOLR *);
    0|]

let yytransl_block = [|
  261 (* INT *);
  263 (* VAR *);
    0|]

let yylhs = "\255\255\
\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\
\002\000\002\000\002\000\002\000\003\000\003\000\003\000\003\000\
\003\000\003\000\003\000\003\000\005\000\005\000\005\000\005\000\
\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
\005\000\005\000\005\000\005\000\004\000\004\000\001\000\000\000"

let yylen = "\002\000\
\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\
\001\000\001\000\001\000\004\000\007\000\001\000\006\000\006\000\
\006\000\006\000\003\000\003\000\012\000\014\000\004\000\010\000\
\006\000\006\000\006\000\008\000\010\000\010\000\010\000\014\000\
\001\000\005\000\003\000\005\000\001\000\002\000\002\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\006\000\000\000\000\000\002\000\003\000\001\000\
\005\000\004\000\000\000\000\000\009\000\008\000\007\000\000\000\
\010\000\011\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\040\000\
\033\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\039\000\000\000\038\000\000\000\000\000\000\000\035\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\019\000\020\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\012\000\000\000\000\000\000\000\
\000\000\000\000\000\000\023\000\000\000\000\000\000\000\000\000\
\000\000\034\000\000\000\000\000\000\000\000\000\036\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\016\000\015\000\018\000\017\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\027\000\025\000\026\000\013\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\028\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\030\000\031\000\000\000\029\000\000\000\
\000\000\024\000\000\000\000\000\000\000\000\000\021\000\000\000\
\000\000\000\000\032\000\022\000"

let yydgoto = "\002\000\
\032\000\033\000\034\000\035\000\036\000"

let yysindex = "\005\000\
\171\255\000\000\000\000\171\255\171\255\000\000\000\000\000\000\
\000\000\000\000\001\255\002\255\000\000\000\000\000\000\171\255\
\000\000\000\000\233\254\003\255\004\255\005\255\006\255\007\255\
\008\255\009\255\010\255\011\255\013\255\014\255\015\255\000\000\
\000\000\013\000\057\000\250\254\251\254\017\255\022\255\023\255\
\025\255\026\255\229\254\030\255\171\255\171\255\171\255\171\255\
\171\255\171\255\171\255\171\255\171\255\171\255\171\255\171\255\
\000\000\171\255\000\000\171\255\057\000\171\255\000\000\171\255\
\171\255\171\255\171\255\171\255\238\254\012\255\033\255\034\255\
\035\255\036\255\037\255\038\255\031\255\040\255\041\255\043\255\
\044\255\045\255\018\255\000\000\000\000\054\255\039\255\049\255\
\050\255\051\255\046\255\048\255\000\000\171\255\171\255\171\255\
\171\255\171\255\171\255\000\000\171\255\171\255\171\255\171\255\
\171\255\000\000\171\255\171\255\171\255\171\255\000\000\171\255\
\064\255\066\255\075\255\078\255\079\255\080\255\081\255\082\255\
\076\255\077\255\083\255\000\000\000\000\000\000\000\000\053\255\
\171\255\171\255\171\255\171\255\171\255\171\255\171\255\171\255\
\000\000\000\000\000\000\000\000\086\255\087\255\088\255\089\255\
\090\255\092\255\093\255\095\255\171\255\171\255\171\255\171\255\
\171\255\171\255\171\255\000\000\101\255\106\255\094\255\108\255\
\096\255\117\255\110\255\000\000\000\000\171\255\000\000\171\255\
\171\255\000\000\119\255\112\255\121\255\171\255\000\000\171\255\
\114\255\115\255\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\051\000\001\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\000\000\007\000\000\000\223\255"

let yytablesize = 369
let yytable = "\060\000\
\037\000\059\000\039\000\041\000\068\000\001\000\069\000\040\000\
\042\000\044\000\037\000\038\000\057\000\045\000\046\000\047\000\
\048\000\049\000\050\000\051\000\052\000\053\000\043\000\054\000\
\055\000\056\000\062\000\085\000\063\000\064\000\065\000\061\000\
\066\000\067\000\070\000\092\000\094\000\095\000\096\000\097\000\
\098\000\099\000\100\000\101\000\102\000\093\000\103\000\104\000\
\105\000\068\000\014\000\071\000\072\000\073\000\074\000\075\000\
\076\000\077\000\078\000\079\000\080\000\081\000\082\000\106\000\
\083\000\107\000\084\000\129\000\086\000\130\000\087\000\088\000\
\089\000\090\000\091\000\108\000\109\000\110\000\131\000\111\000\
\112\000\132\000\133\000\134\000\135\000\136\000\140\000\137\000\
\138\000\149\000\150\000\151\000\152\000\153\000\139\000\154\000\
\155\000\166\000\000\000\168\000\113\000\114\000\115\000\116\000\
\117\000\118\000\156\000\119\000\120\000\121\000\122\000\123\000\
\164\000\124\000\125\000\126\000\127\000\165\000\128\000\167\000\
\169\000\170\000\174\000\175\000\176\000\179\000\180\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\141\000\
\142\000\143\000\144\000\145\000\146\000\147\000\148\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\157\000\158\000\159\000\160\000\161\000\
\162\000\163\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\171\000\000\000\172\000\173\000\
\000\000\003\000\000\000\004\000\177\000\005\000\178\000\006\000\
\007\000\008\000\009\000\010\000\011\000\012\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\013\000\
\014\000\015\000\000\000\016\000\000\000\000\000\000\000\000\000\
\000\000\017\000\018\000\019\000\020\000\021\000\022\000\000\000\
\000\000\023\000\024\000\025\000\026\000\027\000\028\000\029\000\
\000\000\030\000\031\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\037\000\000\000\000\000\037\000\
\000\000\037\000\037\000\037\000\037\000\037\000\037\000\037\000\
\037\000\037\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\037\000\000\000\037\000\037\000\037\000\
\037\000\037\000\037\000\000\000\000\000\000\000\000\000\037\000\
\037\000\037\000\037\000\037\000\037\000\000\000\000\000\037\000\
\037\000\037\000\037\000\037\000\037\000\037\000\014\000\037\000\
\037\000\000\000\000\000\000\000\014\000\000\000\014\000\003\000\
\000\000\004\000\000\000\005\000\000\000\006\000\007\000\008\000\
\009\000\010\000\000\000\000\000\000\000\014\000\000\000\000\000\
\000\000\000\000\014\000\000\000\014\000\013\000\014\000\015\000\
\000\000\058\000\000\000\000\000\000\000\000\000\000\000\017\000\
\018\000\019\000\020\000\021\000\022\000\000\000\000\000\023\000\
\024\000\025\000\026\000\027\000\028\000\029\000\000\000\030\000\
\031\000"

let yycheck = "\006\001\
\000\000\035\000\002\001\002\001\032\001\001\000\034\001\007\001\
\007\001\033\001\004\000\005\000\000\000\011\001\011\001\011\001\
\011\001\011\001\011\001\011\001\011\001\011\001\016\000\011\001\
\011\001\011\001\032\001\061\000\012\001\008\001\008\001\038\001\
\008\001\008\001\005\001\054\001\004\001\004\001\004\001\004\001\
\004\001\004\001\012\001\004\001\004\001\034\001\004\001\004\001\
\004\001\032\001\000\000\045\000\046\000\047\000\048\000\049\000\
\050\000\051\000\052\000\053\000\054\000\055\000\056\000\010\001\
\058\000\027\001\060\000\004\001\062\000\004\001\064\000\065\000\
\066\000\067\000\068\000\027\001\027\001\027\001\004\001\034\001\
\033\001\004\001\004\001\004\001\004\001\004\001\034\001\012\001\
\012\001\004\001\004\001\004\001\004\001\004\001\012\001\004\001\
\004\001\004\001\255\255\004\001\094\000\095\000\096\000\097\000\
\098\000\099\000\012\001\101\000\102\000\103\000\104\000\105\000\
\012\001\107\000\108\000\109\000\110\000\012\001\112\000\012\001\
\004\001\012\001\004\001\012\001\004\001\012\001\012\001\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\129\000\
\130\000\131\000\132\000\133\000\134\000\135\000\136\000\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\149\000\150\000\151\000\152\000\153\000\
\154\000\155\000\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\166\000\255\255\168\000\169\000\
\255\255\007\001\255\255\009\001\174\000\011\001\176\000\013\001\
\014\001\015\001\016\001\017\001\018\001\019\001\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\029\001\
\030\001\031\001\255\255\033\001\255\255\255\255\255\255\255\255\
\255\255\039\001\040\001\041\001\042\001\043\001\044\001\255\255\
\255\255\047\001\048\001\049\001\050\001\051\001\052\001\053\001\
\255\255\055\001\056\001\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\004\001\255\255\255\255\007\001\
\255\255\009\001\010\001\011\001\012\001\013\001\014\001\015\001\
\016\001\017\001\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\027\001\255\255\029\001\030\001\031\001\
\032\001\033\001\034\001\255\255\255\255\255\255\255\255\039\001\
\040\001\041\001\042\001\043\001\044\001\255\255\255\255\047\001\
\048\001\049\001\050\001\051\001\052\001\053\001\004\001\055\001\
\056\001\255\255\255\255\255\255\010\001\255\255\012\001\007\001\
\255\255\009\001\255\255\011\001\255\255\013\001\014\001\015\001\
\016\001\017\001\255\255\255\255\255\255\027\001\255\255\255\255\
\255\255\255\255\032\001\255\255\034\001\029\001\030\001\031\001\
\255\255\033\001\255\255\255\255\255\255\255\255\255\255\039\001\
\040\001\041\001\042\001\043\001\044\001\255\255\255\255\047\001\
\048\001\049\001\050\001\051\001\052\001\053\001\255\255\055\001\
\056\001"

let yynames_const = "\
  LEMMA\000\
  WILDCARD\000\
  EOF\000\
  COMMA\000\
  SEMICOLLON\000\
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
  BAR\000\
  LSQ\000\
  RSQ\000\
  PROD\000\
  LANGLE\000\
  RANGLE\000\
  SUBTYPE\000\
  PROP\000\
  SMALL\000\
  TYPE\000\
  NATREC\000\
  BOOLREC\000\
  SUMBOOLREC\000\
  CONVERT\000\
  EXTRACT\000\
  MEMBERSHIP\000\
  SUBTRANS\000\
  SUBPROD\000\
  SUBREFL\000\
  SUBSUB\000\
  SUBGEN\000\
  SUBUNREFINE\000\
  AMPERSAND\000\
  SBOOLL\000\
  SBOOLR\000\
  "

let yynames_block = "\
  INT\000\
  VAR\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    Obj.repr(
# 55 "lambdaAst.mly"
      ( Nil )
# 392 "lambdaAst.ml"
               : 'const))
; (fun __caml_parser_env ->
    Obj.repr(
# 56 "lambdaAst.mly"
       ( NatO )
# 398 "lambdaAst.ml"
               : 'const))
; (fun __caml_parser_env ->
    Obj.repr(
# 57 "lambdaAst.mly"
       ( NatSucc )
# 404 "lambdaAst.ml"
               : 'const))
; (fun __caml_parser_env ->
    Obj.repr(
# 58 "lambdaAst.mly"
        ( BoolFalse )
# 410 "lambdaAst.ml"
               : 'const))
; (fun __caml_parser_env ->
    Obj.repr(
# 59 "lambdaAst.mly"
       ( BoolTrue )
# 416 "lambdaAst.ml"
               : 'const))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 60 "lambdaAst.mly"
      ( Var _1 )
# 423 "lambdaAst.ml"
               : 'const))
; (fun __caml_parser_env ->
    Obj.repr(
# 61 "lambdaAst.mly"
      ( Nat )
# 429 "lambdaAst.ml"
               : 'const))
; (fun __caml_parser_env ->
    Obj.repr(
# 62 "lambdaAst.mly"
       ( Bool )
# 435 "lambdaAst.ml"
               : 'const))
; (fun __caml_parser_env ->
    Obj.repr(
# 63 "lambdaAst.mly"
       ( Unit )
# 441 "lambdaAst.ml"
               : 'const))
; (fun __caml_parser_env ->
    Obj.repr(
# 64 "lambdaAst.mly"
       ( Prop )
# 447 "lambdaAst.ml"
               : 'const))
; (fun __caml_parser_env ->
    Obj.repr(
# 65 "lambdaAst.mly"
        ( Small )
# 453 "lambdaAst.ml"
               : 'const))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : int) in
    Obj.repr(
# 66 "lambdaAst.mly"
                   ( Type _3 )
# 460 "lambdaAst.ml"
               : 'const))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : 'term) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 68 "lambdaAst.mly"
                                      ( Sumbool (_2, _6) )
# 468 "lambdaAst.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'app_term) in
    Obj.repr(
# 69 "lambdaAst.mly"
           ( _1 )
# 475 "lambdaAst.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 70 "lambdaAst.mly"
                                 ( Abs (_2, _4, _6) )
# 484 "lambdaAst.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 71 "lambdaAst.mly"
                                      ( Abs ("_", _4, _6) )
# 492 "lambdaAst.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 72 "lambdaAst.mly"
                                  ( Forall (_2, _4, _6) )
# 501 "lambdaAst.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 73 "lambdaAst.mly"
                                       ( Forall ("_", _4, _6) )
# 509 "lambdaAst.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'atom_term) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 74 "lambdaAst.mly"
                       ( Forall ("_", _1, _3) )
# 517 "lambdaAst.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'atom_term) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'atom_term) in
    Obj.repr(
# 75 "lambdaAst.mly"
                              ( Subtyping (_1, _3) )
# 525 "lambdaAst.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 9 : 'term) in
    let _5 = (Parsing.peek_val __caml_parser_env 7 : 'term) in
    let _7 = (Parsing.peek_val __caml_parser_env 5 : 'term) in
    let _9 = (Parsing.peek_val __caml_parser_env 3 : 'term) in
    let _11 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 77 "lambdaAst.mly"
                                                                                              ( SubTrans (_3, _5, _7, _9, _11) )
# 536 "lambdaAst.ml"
               : 'atom_term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 11 : 'term) in
    let _5 = (Parsing.peek_val __caml_parser_env 9 : 'term) in
    let _7 = (Parsing.peek_val __caml_parser_env 7 : 'term) in
    let _9 = (Parsing.peek_val __caml_parser_env 5 : 'term) in
    let _11 = (Parsing.peek_val __caml_parser_env 3 : 'term) in
    let _13 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 78 "lambdaAst.mly"
                                                                                                             ( SubProd (_3, _5, _7, _9, _11, _13) )
# 548 "lambdaAst.ml"
               : 'atom_term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 79 "lambdaAst.mly"
                             ( SubRefl _3 )
# 555 "lambdaAst.ml"
               : 'atom_term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 7 : 'term) in
    let _5 = (Parsing.peek_val __caml_parser_env 5 : 'term) in
    let _7 = (Parsing.peek_val __caml_parser_env 3 : 'term) in
    let _9 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 80 "lambdaAst.mly"
                                                                            ( SubSub (_3, _5, _7, _9) )
# 565 "lambdaAst.ml"
               : 'atom_term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'term) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 81 "lambdaAst.mly"
                                            ( SBLeft (_3, _5) )
# 573 "lambdaAst.ml"
               : 'atom_term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'term) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 82 "lambdaAst.mly"
                                            ( SBRight (_3, _5) )
# 581 "lambdaAst.ml"
               : 'atom_term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'term) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 83 "lambdaAst.mly"
                                                 ( SubUnrefine (_3, _5) )
# 589 "lambdaAst.ml"
               : 'atom_term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : 'term) in
    let _5 = (Parsing.peek_val __caml_parser_env 3 : 'term) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 84 "lambdaAst.mly"
                                                            ( SubGen (_3, _5, _7) )
# 598 "lambdaAst.ml"
               : 'atom_term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 7 : 'term) in
    let _5 = (Parsing.peek_val __caml_parser_env 5 : 'term) in
    let _7 = (Parsing.peek_val __caml_parser_env 3 : 'term) in
    let _9 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 85 "lambdaAst.mly"
                                                                                ( Membership (_3, _5, _7, _9) )
# 608 "lambdaAst.ml"
               : 'atom_term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 7 : 'term) in
    let _5 = (Parsing.peek_val __caml_parser_env 5 : 'term) in
    let _7 = (Parsing.peek_val __caml_parser_env 3 : 'term) in
    let _9 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 86 "lambdaAst.mly"
                                                                            ( NatRec (_3, _5, _7, _9) )
# 618 "lambdaAst.ml"
               : 'atom_term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 7 : 'term) in
    let _5 = (Parsing.peek_val __caml_parser_env 5 : 'term) in
    let _7 = (Parsing.peek_val __caml_parser_env 3 : 'term) in
    let _9 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 87 "lambdaAst.mly"
                                                                             ( BoolRec (_3, _5, _7, _9) )
# 628 "lambdaAst.ml"
               : 'atom_term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 11 : 'term) in
    let _5 = (Parsing.peek_val __caml_parser_env 9 : 'term) in
    let _7 = (Parsing.peek_val __caml_parser_env 7 : 'term) in
    let _9 = (Parsing.peek_val __caml_parser_env 5 : 'term) in
    let _11 = (Parsing.peek_val __caml_parser_env 3 : 'term) in
    let _13 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 88 "lambdaAst.mly"
                                                                                                                ( SumboolRec (_3, _5, _7, _9, _11, _13) )
# 640 "lambdaAst.ml"
               : 'atom_term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'const) in
    Obj.repr(
# 89 "lambdaAst.mly"
        ( _1 )
# 647 "lambdaAst.ml"
               : 'atom_term))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'term) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 90 "lambdaAst.mly"
                              ( Refine (_2, _4) )
# 655 "lambdaAst.ml"
               : 'atom_term))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 91 "lambdaAst.mly"
                     ( _2 )
# 662 "lambdaAst.ml"
               : 'atom_term))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'term) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 92 "lambdaAst.mly"
                        ( Sumbool (_2, _4) )
# 670 "lambdaAst.ml"
               : 'atom_term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'atom_term) in
    Obj.repr(
# 94 "lambdaAst.mly"
            ( _1 )
# 677 "lambdaAst.ml"
               : 'app_term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'app_term) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'atom_term) in
    Obj.repr(
# 95 "lambdaAst.mly"
                     ( App (_1, _2) )
# 685 "lambdaAst.ml"
               : 'app_term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 97 "lambdaAst.mly"
           ( _1 )
# 692 "lambdaAst.ml"
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
