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
\004\000\004\000\004\000\004\000\004\000\004\000\004\000\004\000\
\004\000\004\000\007\000\007\000\007\000\007\000\007\000\006\000\
\006\000\006\000\006\000\006\000\006\000\008\000\008\000\005\000\
\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
\005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
\009\000\009\000\009\000\009\000\010\000\010\000\010\000\010\000\
\001\000\002\000\003\000\000\000\000\000\000\000"

let yylen = "\002\000\
\001\000\001\000\003\000\003\000\003\000\003\000\005\000\006\000\
\006\000\004\000\001\000\001\000\001\000\001\000\003\000\001\000\
\003\000\007\000\004\000\007\000\001\000\003\000\003\000\001\000\
\001\000\001\000\001\000\001\000\001\000\003\000\008\000\008\000\
\007\000\007\000\003\000\003\000\013\000\012\000\010\000\009\000\
\002\000\002\000\004\000\004\000\001\000\001\000\003\000\003\000\
\002\000\002\000\002\000\002\000\002\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\029\000\000\000\025\000\026\000\
\024\000\028\000\027\000\000\000\000\000\000\000\052\000\000\000\
\014\000\000\000\000\000\000\000\012\000\011\000\013\000\053\000\
\000\000\000\000\021\000\000\000\000\000\000\000\001\000\002\000\
\054\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\049\000\000\000\000\000\000\000\000\000\
\000\000\050\000\000\000\000\000\000\000\000\000\000\000\000\000\
\051\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\030\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\036\000\035\000\000\000\000\000\015\000\000\000\
\017\000\000\000\000\000\023\000\003\000\000\000\000\000\000\000\
\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\048\000\047\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\044\000\043\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\034\000\033\000\000\000\000\000\000\000\000\000\
\020\000\018\000\032\000\031\000\000\000\000\000\000\000\000\000\
\040\000\000\000\000\000\000\000\000\000\039\000\000\000\000\000\
\000\000\038\000\000\000\037\000"

let yydgoto = "\004\000\
\015\000\024\000\033\000\034\000\035\000\048\000\026\000\027\000\
\038\000\043\000"

let yysindex = "\150\000\
\065\001\056\255\168\000\000\000\000\000\016\255\000\000\000\000\
\000\000\000\000\000\000\065\001\065\001\065\001\000\000\002\000\
\000\000\003\255\094\255\010\255\000\000\000\000\000\000\000\000\
\003\000\237\254\000\000\146\000\046\255\050\255\000\000\000\000\
\000\000\038\000\125\255\001\255\253\000\019\001\252\254\024\255\
\215\255\089\000\021\255\000\000\071\255\075\255\088\255\156\255\
\074\255\000\000\056\255\104\255\105\255\189\000\039\255\100\255\
\000\000\168\000\168\000\168\000\065\001\133\255\163\255\102\000\
\151\255\102\000\000\000\151\255\195\255\168\000\200\255\168\000\
\065\001\065\001\000\000\000\000\056\255\056\255\000\000\056\255\
\000\000\056\255\237\254\000\000\000\000\056\255\168\000\056\255\
\000\000\161\255\180\255\188\255\056\255\191\255\000\000\132\000\
\175\255\178\255\065\001\208\255\065\001\211\255\000\000\000\000\
\253\254\179\255\221\255\034\255\086\255\045\255\056\255\087\255\
\065\001\088\255\000\000\000\000\027\255\218\255\084\255\217\255\
\168\000\240\255\168\000\168\000\221\255\065\001\211\000\033\001\
\241\255\242\255\228\255\243\255\051\255\056\255\086\255\086\255\
\233\000\051\001\000\000\000\000\065\001\065\001\244\255\065\001\
\000\000\000\000\000\000\000\000\112\255\115\255\065\001\116\255\
\000\000\245\255\121\255\235\255\065\001\000\000\250\255\148\255\
\065\001\000\000\150\255\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\219\255\225\255\000\000\000\000\000\000\000\000\007\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\182\255\000\000\000\000\199\255\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\
\000\000\009\000\045\000\000\000\000\000\000\000\160\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\012\000\000\000\013\000\000\000\000\000\000\000\
\000\000\160\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\040\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\051\000\052\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\000\000\000\000\037\000\005\000\006\000\205\000\206\000\
\008\000\167\000"

let yytablesize = 616
let yytable = "\051\000\
\016\000\044\000\050\000\022\000\062\000\016\000\046\000\025\000\
\005\000\014\000\037\000\019\000\010\000\049\000\069\000\014\000\
\039\000\040\000\041\000\005\000\063\000\042\000\052\000\006\000\
\045\000\007\000\008\000\009\000\010\000\011\000\012\000\013\000\
\054\000\129\000\121\000\036\000\051\000\057\000\070\000\007\000\
\071\000\065\000\068\000\086\000\006\000\065\000\068\000\051\000\
\014\000\055\000\008\000\009\000\045\000\056\000\014\000\045\000\
\081\000\145\000\065\000\017\000\075\000\018\000\123\000\019\000\
\053\000\092\000\072\000\087\000\037\000\097\000\037\000\098\000\
\076\000\124\000\058\000\059\000\020\000\041\000\041\000\077\000\
\042\000\042\000\105\000\106\000\060\000\107\000\021\000\022\000\
\023\000\051\000\131\000\108\000\078\000\110\000\089\000\090\000\
\091\000\047\000\112\000\018\000\037\000\019\000\080\000\117\000\
\088\000\119\000\100\000\017\000\102\000\058\000\059\000\082\000\
\045\000\085\000\020\000\126\000\125\000\127\000\153\000\060\000\
\128\000\154\000\156\000\109\000\021\000\022\000\023\000\158\000\
\058\000\059\000\137\000\065\000\068\000\138\000\021\000\022\000\
\023\000\093\000\060\000\146\000\045\000\065\000\068\000\045\000\
\045\000\149\000\150\000\061\000\152\000\045\000\001\000\002\000\
\003\000\045\000\162\000\155\000\164\000\133\000\051\000\135\000\
\136\000\160\000\014\000\029\000\079\000\163\000\094\000\029\000\
\014\000\029\000\029\000\029\000\029\000\029\000\029\000\029\000\
\045\000\051\000\045\000\045\000\051\000\051\000\041\000\115\000\
\058\000\041\000\116\000\122\000\029\000\041\000\041\000\041\000\
\041\000\041\000\041\000\041\000\041\000\041\000\029\000\042\000\
\099\000\014\000\042\000\058\000\059\000\101\000\042\000\042\000\
\042\000\042\000\042\000\042\000\042\000\042\000\042\000\073\000\
\045\000\111\000\005\000\113\000\041\000\041\000\064\000\051\000\
\007\000\008\000\009\000\010\000\011\000\012\000\013\000\058\000\
\059\000\132\000\058\000\059\000\130\000\042\000\042\000\103\000\
\104\000\060\000\134\000\045\000\060\000\143\000\141\000\142\000\
\144\000\151\000\157\000\118\000\159\000\014\000\120\000\161\000\
\083\000\084\000\046\000\016\000\000\000\051\000\022\000\016\000\
\045\000\016\000\022\000\000\000\022\000\000\000\000\000\005\000\
\000\000\005\000\019\000\010\000\019\000\010\000\000\000\000\000\
\016\000\016\000\000\000\022\000\022\000\016\000\045\000\000\000\
\022\000\005\000\016\000\019\000\019\000\022\000\016\000\000\000\
\019\000\022\000\005\000\000\000\016\000\019\000\007\000\022\000\
\007\000\019\000\000\000\006\000\005\000\006\000\000\000\019\000\
\010\000\008\000\009\000\008\000\009\000\058\000\059\000\007\000\
\007\000\000\000\000\000\000\000\000\000\000\000\000\000\060\000\
\000\000\007\000\000\000\000\000\000\000\000\000\006\000\000\000\
\000\000\000\000\000\000\007\000\000\000\000\000\000\000\000\000\
\006\000\074\000\000\000\000\000\005\000\000\000\008\000\009\000\
\066\000\000\000\007\000\008\000\009\000\010\000\011\000\012\000\
\013\000\095\000\000\000\018\000\000\000\096\000\000\000\007\000\
\008\000\009\000\010\000\011\000\012\000\013\000\000\000\000\000\
\000\000\036\000\020\000\000\000\000\000\000\000\000\000\014\000\
\000\000\000\000\000\000\000\000\021\000\022\000\023\000\114\000\
\000\000\018\000\000\000\096\000\014\000\007\000\008\000\009\000\
\010\000\011\000\012\000\013\000\000\000\005\000\000\000\036\000\
\020\000\028\000\000\000\007\000\008\000\009\000\010\000\011\000\
\012\000\013\000\021\000\022\000\023\000\036\000\029\000\030\000\
\000\000\000\000\014\000\005\000\031\000\032\000\000\000\028\000\
\000\000\007\000\008\000\009\000\010\000\011\000\012\000\013\000\
\014\000\000\000\000\000\000\000\029\000\030\000\000\000\000\000\
\005\000\000\000\031\000\032\000\064\000\000\000\007\000\008\000\
\009\000\010\000\011\000\012\000\013\000\000\000\014\000\000\000\
\000\000\000\000\000\000\061\000\000\000\000\000\005\000\000\000\
\000\000\045\000\064\000\139\000\007\000\008\000\009\000\010\000\
\011\000\012\000\013\000\014\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\005\000\000\000\000\000\045\000\
\064\000\147\000\007\000\008\000\009\000\010\000\011\000\012\000\
\013\000\014\000\000\000\000\000\000\000\000\000\000\000\000\000\
\005\000\000\000\000\000\000\000\064\000\045\000\007\000\008\000\
\009\000\010\000\011\000\012\000\013\000\000\000\000\000\014\000\
\000\000\000\000\000\000\000\000\000\000\000\000\005\000\000\000\
\000\000\045\000\066\000\067\000\007\000\008\000\009\000\010\000\
\011\000\012\000\013\000\014\000\005\000\000\000\000\000\000\000\
\066\000\140\000\007\000\008\000\009\000\010\000\011\000\012\000\
\013\000\000\000\000\000\000\000\000\000\000\000\005\000\000\000\
\000\000\014\000\066\000\148\000\007\000\008\000\009\000\010\000\
\011\000\012\000\013\000\000\000\005\000\000\000\000\000\014\000\
\006\000\000\000\007\000\008\000\009\000\010\000\011\000\012\000\
\013\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\014\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\014\000"

let yycheck = "\003\001\
\000\000\000\000\000\000\000\000\004\001\001\000\004\001\002\000\
\000\000\003\001\006\000\000\000\000\000\004\001\019\001\009\001\
\012\000\013\000\014\000\004\001\020\001\014\000\042\001\008\001\
\029\001\010\001\011\001\012\001\013\001\014\001\015\001\016\001\
\028\000\007\001\038\001\020\001\003\001\000\000\043\001\000\000\
\017\001\037\000\038\000\005\001\000\000\041\000\042\000\003\001\
\042\001\004\001\000\000\000\000\029\001\004\001\039\001\029\001\
\051\000\007\001\054\000\004\001\040\001\006\001\029\001\008\001\
\028\000\061\000\043\001\029\001\064\000\064\000\066\000\066\000\
\002\001\029\001\024\001\025\001\021\001\073\000\074\000\005\001\
\073\000\074\000\077\000\078\000\034\001\080\000\031\001\032\001\
\033\001\003\001\007\001\086\000\005\001\088\000\058\000\059\000\
\060\000\004\001\093\000\006\001\096\000\008\001\029\001\099\000\
\005\001\101\000\070\000\004\001\072\000\024\001\025\001\008\001\
\029\001\009\001\021\001\029\001\111\000\113\000\007\001\034\001\
\113\000\007\001\007\001\087\000\031\001\032\001\033\001\007\001\
\024\001\025\001\126\000\127\000\128\000\126\000\031\001\032\001\
\033\001\005\001\034\001\134\000\029\001\137\000\138\000\029\001\
\029\001\141\000\142\000\023\001\144\000\029\001\001\000\002\000\
\003\000\029\001\007\001\151\000\007\001\121\000\003\001\123\000\
\124\000\157\000\003\001\004\001\009\001\161\000\004\001\008\001\
\009\001\010\001\011\001\012\001\013\001\014\001\015\001\016\001\
\029\001\003\001\029\001\029\001\003\001\003\001\001\001\009\001\
\024\001\004\001\009\001\009\001\029\001\008\001\009\001\010\001\
\011\001\012\001\013\001\014\001\015\001\016\001\039\001\001\001\
\006\001\042\001\004\001\024\001\025\001\006\001\008\001\009\001\
\010\001\011\001\012\001\013\001\014\001\015\001\016\001\001\001\
\029\001\030\001\004\001\029\001\039\001\040\001\008\001\003\001\
\010\001\011\001\012\001\013\001\014\001\015\001\016\001\024\001\
\025\001\017\001\024\001\025\001\019\001\039\001\040\001\073\000\
\074\000\034\001\003\001\029\001\034\001\018\001\006\001\006\001\
\006\001\006\001\006\001\044\001\018\001\039\001\044\001\006\001\
\052\000\052\000\040\001\003\001\255\255\003\001\003\001\007\001\
\040\001\009\001\007\001\255\255\009\001\255\255\255\255\007\001\
\255\255\009\001\007\001\007\001\009\001\009\001\255\255\255\255\
\024\001\025\001\255\255\024\001\025\001\029\001\029\001\255\255\
\029\001\025\001\034\001\024\001\025\001\034\001\038\001\255\255\
\029\001\038\001\034\001\255\255\044\001\034\001\007\001\044\001\
\009\001\038\001\255\255\007\001\044\001\009\001\255\255\044\001\
\044\001\007\001\007\001\009\001\009\001\024\001\025\001\024\001\
\025\001\255\255\255\255\255\255\255\255\255\255\255\255\034\001\
\255\255\034\001\255\255\255\255\255\255\255\255\034\001\255\255\
\255\255\255\255\255\255\044\001\255\255\255\255\255\255\255\255\
\044\001\001\001\255\255\255\255\004\001\255\255\044\001\044\001\
\008\001\255\255\010\001\011\001\012\001\013\001\014\001\015\001\
\016\001\004\001\255\255\006\001\255\255\008\001\255\255\010\001\
\011\001\012\001\013\001\014\001\015\001\016\001\255\255\255\255\
\255\255\020\001\021\001\255\255\255\255\255\255\255\255\039\001\
\255\255\255\255\255\255\255\255\031\001\032\001\033\001\004\001\
\255\255\006\001\255\255\008\001\039\001\010\001\011\001\012\001\
\013\001\014\001\015\001\016\001\255\255\004\001\255\255\020\001\
\021\001\008\001\255\255\010\001\011\001\012\001\013\001\014\001\
\015\001\016\001\031\001\032\001\033\001\020\001\021\001\022\001\
\255\255\255\255\039\001\004\001\027\001\028\001\255\255\008\001\
\255\255\010\001\011\001\012\001\013\001\014\001\015\001\016\001\
\039\001\255\255\255\255\255\255\021\001\022\001\255\255\255\255\
\004\001\255\255\027\001\028\001\008\001\255\255\010\001\011\001\
\012\001\013\001\014\001\015\001\016\001\255\255\039\001\255\255\
\255\255\255\255\255\255\023\001\255\255\255\255\004\001\255\255\
\255\255\029\001\008\001\009\001\010\001\011\001\012\001\013\001\
\014\001\015\001\016\001\039\001\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\004\001\255\255\255\255\029\001\
\008\001\009\001\010\001\011\001\012\001\013\001\014\001\015\001\
\016\001\039\001\255\255\255\255\255\255\255\255\255\255\255\255\
\004\001\255\255\255\255\255\255\008\001\029\001\010\001\011\001\
\012\001\013\001\014\001\015\001\016\001\255\255\255\255\039\001\
\255\255\255\255\255\255\255\255\255\255\255\255\004\001\255\255\
\255\255\029\001\008\001\009\001\010\001\011\001\012\001\013\001\
\014\001\015\001\016\001\039\001\004\001\255\255\255\255\255\255\
\008\001\009\001\010\001\011\001\012\001\013\001\014\001\015\001\
\016\001\255\255\255\255\255\255\255\255\255\255\004\001\255\255\
\255\255\039\001\008\001\009\001\010\001\011\001\012\001\013\001\
\014\001\015\001\016\001\255\255\004\001\255\255\255\255\039\001\
\008\001\255\255\010\001\011\001\012\001\013\001\014\001\015\001\
\016\001\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\039\001\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\039\001"

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
# 53 "lambdaAst.mly"
      ( Top )
# 416 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    Obj.repr(
# 54 "lambdaAst.mly"
      ( Bot )
# 422 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'prop_grammar) in
    Obj.repr(
# 55 "lambdaAst.mly"
                             ( _2 )
# 429 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'prop_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'prop_grammar) in
    Obj.repr(
# 56 "lambdaAst.mly"
                                     ( Conjunction (_1, _3) )
# 437 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'prop_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'prop_grammar) in
    Obj.repr(
# 57 "lambdaAst.mly"
                                    ( Disjunction (_1, _3) )
# 445 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'prop_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'prop_grammar) in
    Obj.repr(
# 58 "lambdaAst.mly"
                                                         ( Implication (_1, _3) )
# 453 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : 'term_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'term_grammar) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'type_grammar) in
    Obj.repr(
# 59 "lambdaAst.mly"
                                                      ( Eq (_1, _3, _5) )
# 462 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'type_grammar) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'prop_grammar) in
    Obj.repr(
# 60 "lambdaAst.mly"
                                                                 ( Forall (_2, _4, _6) )
# 471 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'type_grammar) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'prop_grammar) in
    Obj.repr(
# 61 "lambdaAst.mly"
                                                                 ( Exists (_2, _4, _6) )
# 480 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'prop_grammar) in
    Obj.repr(
# 62 "lambdaAst.mly"
                                             ( ForallGen (_2, _4) )
# 488 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    Obj.repr(
# 64 "lambdaAst.mly"
       ( Bool )
# 494 "lambdaAst.ml"
               : 'atom_type_grammar))
; (fun __caml_parser_env ->
    Obj.repr(
# 65 "lambdaAst.mly"
       ( Unit )
# 500 "lambdaAst.ml"
               : 'atom_type_grammar))
; (fun __caml_parser_env ->
    Obj.repr(
# 66 "lambdaAst.mly"
      ( Nat )
# 506 "lambdaAst.ml"
               : 'atom_type_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 67 "lambdaAst.mly"
      ( TVar _1 )
# 513 "lambdaAst.ml"
               : 'atom_type_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'type_grammar) in
    Obj.repr(
# 68 "lambdaAst.mly"
                             ( _2 )
# 520 "lambdaAst.ml"
               : 'atom_type_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'atom_type_grammar) in
    Obj.repr(
# 70 "lambdaAst.mly"
                    ( _1 )
# 527 "lambdaAst.ml"
               : 'type_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'type_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'type_grammar) in
    Obj.repr(
# 71 "lambdaAst.mly"
                                                   ( Map ("_", _1, _3) )
# 535 "lambdaAst.ml"
               : 'type_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : 'type_grammar) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'type_grammar) in
    Obj.repr(
# 72 "lambdaAst.mly"
                                                                          ( Map (_2, _4, _7) )
# 544 "lambdaAst.ml"
               : 'type_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'type_grammar) in
    Obj.repr(
# 73 "lambdaAst.mly"
                                                 ( Gen (_2, _4) )
# 552 "lambdaAst.ml"
               : 'type_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : 'type_grammar) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'prop_grammar) in
    Obj.repr(
# 74 "lambdaAst.mly"
                                                                            ( Refine (_2, _4, _6) )
# 561 "lambdaAst.ml"
               : 'type_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'prod_type) in
    Obj.repr(
# 75 "lambdaAst.mly"
                       ( Prod _1 )
# 568 "lambdaAst.ml"
               : 'type_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'atom_type_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'atom_type_grammar) in
    Obj.repr(
# 77 "lambdaAst.mly"
                                           ( [_1; _3] )
# 576 "lambdaAst.ml"
               : 'prod_type))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'atom_type_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'prod_type) in
    Obj.repr(
# 78 "lambdaAst.mly"
                                   ( _1 :: _3 )
# 584 "lambdaAst.ml"
               : 'prod_type))
; (fun __caml_parser_env ->
    Obj.repr(
# 80 "lambdaAst.mly"
      ( Nil )
# 590 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    Obj.repr(
# 81 "lambdaAst.mly"
       ( NatO )
# 596 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    Obj.repr(
# 82 "lambdaAst.mly"
       ( NatSucc )
# 602 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    Obj.repr(
# 83 "lambdaAst.mly"
        ( False )
# 608 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    Obj.repr(
# 84 "lambdaAst.mly"
       ( True )
# 614 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 85 "lambdaAst.mly"
      ( Var _1 )
# 621 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'app_term_grammar) in
    Obj.repr(
# 86 "lambdaAst.mly"
                                 ( _2 )
# 628 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 3 : 'type_grammar) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'app_term_grammar) in
    Obj.repr(
# 87 "lambdaAst.mly"
                                                                   ( Abs (_3, _5, _7) )
# 637 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 3 : 'type_grammar) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'term_grammar) in
    Obj.repr(
# 88 "lambdaAst.mly"
                                                               ( Abs (_3, _5, _7) )
# 646 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _4 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'app_term_grammar) in
    Obj.repr(
# 89 "lambdaAst.mly"
                                                     ( Generic (_4, _6) )
# 654 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _4 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'term_grammar) in
    Obj.repr(
# 90 "lambdaAst.mly"
                                                 ( Generic (_4, _6) )
# 662 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'term_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 91 "lambdaAst.mly"
                       ( Proj (_1, _3) )
# 670 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'term_list) in
    Obj.repr(
# 92 "lambdaAst.mly"
                    ( Tuple _2 )
# 677 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 11 : 'term_grammar) in
    let _4 = (Parsing.peek_val __caml_parser_env 9 : 'prop_grammar) in
    let _8 = (Parsing.peek_val __caml_parser_env 5 : 'term_grammar) in
    let _12 = (Parsing.peek_val __caml_parser_env 1 : 'term_grammar) in
    Obj.repr(
# 93 "lambdaAst.mly"
                                                                                                             ( Ite (_2, _8, _12, _4) )
# 687 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 10 : 'term_grammar) in
    let _4 = (Parsing.peek_val __caml_parser_env 8 : 'prop_grammar) in
    let _8 = (Parsing.peek_val __caml_parser_env 4 : 'term_grammar) in
    let _11 = (Parsing.peek_val __caml_parser_env 1 : 'term_grammar) in
    Obj.repr(
# 94 "lambdaAst.mly"
                                                                                                       ( For (_2, _8, _11, _4) )
# 697 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 8 : 'term_grammar) in
    let _5 = (Parsing.peek_val __caml_parser_env 5 : 'term_grammar) in
    let _9 = (Parsing.peek_val __caml_parser_env 1 : 'term_grammar) in
    Obj.repr(
# 95 "lambdaAst.mly"
                                                                                  ( Ite (_2, _5, _9, Top) )
# 706 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 7 : 'term_grammar) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : 'term_grammar) in
    let _8 = (Parsing.peek_val __caml_parser_env 1 : 'term_grammar) in
    Obj.repr(
# 96 "lambdaAst.mly"
                                                                            ( For (_2, _5, _8, Top) )
# 715 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'term_grammar) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'term_grammar) in
    Obj.repr(
# 98 "lambdaAst.mly"
                                      ( App (_1, _2) )
# 723 "lambdaAst.ml"
               : 'app_term_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'app_term_grammar) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'term_grammar) in
    Obj.repr(
# 99 "lambdaAst.mly"
                                          ( App (_1, _2) )
# 731 "lambdaAst.ml"
               : 'app_term_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'app_term_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'type_grammar) in
    Obj.repr(
# 100 "lambdaAst.mly"
                                                        ( TApp (_1, _3) )
# 739 "lambdaAst.ml"
               : 'app_term_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'term_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'type_grammar) in
    Obj.repr(
# 101 "lambdaAst.mly"
                                                    ( TApp (_1, _3) )
# 747 "lambdaAst.ml"
               : 'app_term_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'app_term_grammar) in
    Obj.repr(
# 103 "lambdaAst.mly"
                   ( [_1] )
# 754 "lambdaAst.ml"
               : 'term_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'term_grammar) in
    Obj.repr(
# 104 "lambdaAst.mly"
               ( [_1] )
# 761 "lambdaAst.ml"
               : 'term_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'app_term_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'term_list) in
    Obj.repr(
# 105 "lambdaAst.mly"
                                   ( _1 :: _3 )
# 769 "lambdaAst.ml"
               : 'term_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'term_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'term_list) in
    Obj.repr(
# 106 "lambdaAst.mly"
                               ( _1 :: _3 )
# 777 "lambdaAst.ml"
               : 'term_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'term_grammar) in
    Obj.repr(
# 108 "lambdaAst.mly"
                   ( _1 )
# 784 "lambdaAst.ml"
               : PreIr.term_ast))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'type_grammar) in
    Obj.repr(
# 110 "lambdaAst.mly"
                   ( _1 )
# 791 "lambdaAst.ml"
               : PreIr.type_ast))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'prop_grammar) in
    Obj.repr(
# 112 "lambdaAst.mly"
                   ( _1 )
# 798 "lambdaAst.ml"
               : PreIr.prop_ast))
(* Entry lambda_term *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
(* Entry lambda_type *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
(* Entry lambda_prop *)
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
let lambda_type (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 2 lexfun lexbuf : PreIr.type_ast)
let lambda_prop (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 3 lexfun lexbuf : PreIr.prop_ast)
