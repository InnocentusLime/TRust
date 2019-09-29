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
\005\000\005\000\005\000\005\000\005\000\005\000\005\000\009\000\
\009\000\009\000\009\000\010\000\010\000\010\000\010\000\001\000\
\002\000\003\000\000\000\000\000\000\000"

let yylen = "\002\000\
\001\000\001\000\003\000\003\000\003\000\003\000\005\000\006\000\
\006\000\004\000\001\000\001\000\001\000\001\000\003\000\001\000\
\003\000\007\000\004\000\007\000\001\000\003\000\003\000\001\000\
\001\000\001\000\001\000\001\000\003\000\008\000\008\000\007\000\
\007\000\003\000\003\000\013\000\012\000\010\000\009\000\002\000\
\002\000\004\000\004\000\001\000\001\000\003\000\003\000\002\000\
\002\000\002\000\002\000\002\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\028\000\000\000\024\000\025\000\
\027\000\026\000\000\000\000\000\000\000\051\000\000\000\014\000\
\000\000\000\000\000\000\012\000\011\000\013\000\052\000\000\000\
\000\000\021\000\000\000\000\000\000\000\001\000\002\000\053\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\048\000\000\000\000\000\000\000\000\000\000\000\
\049\000\000\000\000\000\000\000\000\000\000\000\000\000\050\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\029\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\035\000\034\000\000\000\000\000\015\000\000\000\017\000\
\000\000\000\000\023\000\003\000\000\000\000\000\000\000\004\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\047\000\046\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\043\000\042\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\033\000\032\000\000\000\000\000\000\000\000\000\020\000\
\018\000\031\000\030\000\000\000\000\000\000\000\000\000\039\000\
\000\000\000\000\000\000\000\000\038\000\000\000\000\000\000\000\
\037\000\000\000\036\000"

let yydgoto = "\004\000\
\014\000\023\000\032\000\033\000\034\000\047\000\025\000\026\000\
\037\000\042\000"

let yysindex = "\255\000\
\005\001\055\255\159\000\000\000\000\000\011\255\000\000\000\000\
\000\000\000\000\005\001\005\001\005\001\000\000\002\000\000\000\
\058\255\114\255\065\255\000\000\000\000\000\000\000\000\003\000\
\030\255\000\000\137\000\075\255\080\255\000\000\000\000\000\000\
\038\000\132\255\051\255\214\000\107\000\163\255\017\255\203\255\
\220\255\064\255\000\000\107\255\106\255\111\255\161\255\094\255\
\000\000\055\255\117\255\042\000\180\000\012\255\119\255\000\000\
\159\000\159\000\159\000\005\001\135\255\152\255\093\000\130\255\
\093\000\000\000\130\255\162\255\159\000\183\255\159\000\005\001\
\005\001\000\000\000\000\055\255\055\255\000\000\055\255\000\000\
\055\255\030\255\000\000\000\000\055\255\159\000\055\255\000\000\
\148\255\245\254\084\255\055\255\147\255\000\000\123\000\166\255\
\235\255\005\001\044\000\005\001\046\000\000\000\000\000\005\255\
\236\255\188\255\013\255\245\254\062\255\055\255\070\255\005\001\
\111\255\000\000\000\000\003\255\174\255\004\255\181\255\159\000\
\200\255\159\000\159\000\188\255\005\001\239\255\231\000\199\255\
\202\255\194\255\209\255\068\255\055\255\245\254\245\254\197\000\
\246\000\000\000\000\000\005\001\005\001\214\255\005\001\000\000\
\000\000\000\000\000\000\049\255\067\255\005\001\078\255\000\000\
\221\255\101\255\211\255\005\001\000\000\231\255\134\255\005\001\
\000\000\159\255\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\201\255\
\206\255\000\000\000\000\000\000\000\000\253\254\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\170\255\
\000\000\000\000\186\255\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\004\000\000\000\000\000\000\000\000\000\000\000\000\000\
\009\000\045\000\000\000\000\000\000\000\123\255\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\012\000\000\000\048\000\000\000\000\000\000\000\000\000\
\123\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\040\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\051\000\052\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\000\000\000\000\234\255\017\000\018\000\189\000\200\000\
\250\255\150\000"

let yytablesize = 556
let yytable = "\014\000\
\016\000\043\000\049\000\022\000\052\000\014\000\041\000\050\000\
\005\000\128\000\130\000\019\000\057\000\058\000\005\000\050\000\
\085\000\015\000\006\000\024\000\007\000\008\000\036\000\009\000\
\010\000\011\000\012\000\038\000\039\000\040\000\035\000\044\000\
\044\000\070\000\088\000\089\000\090\000\056\000\014\000\007\000\
\086\000\122\000\120\000\053\000\006\000\044\000\099\000\010\000\
\101\000\013\000\008\000\009\000\064\000\067\000\061\000\152\000\
\064\000\067\000\016\000\071\000\017\000\045\000\018\000\108\000\
\050\000\041\000\041\000\080\000\048\000\064\000\062\000\051\000\
\050\000\153\000\144\000\019\000\091\000\044\000\054\000\036\000\
\096\000\036\000\097\000\055\000\155\000\020\000\021\000\022\000\
\040\000\040\000\123\000\057\000\058\000\104\000\105\000\044\000\
\106\000\132\000\125\000\134\000\135\000\059\000\107\000\074\000\
\109\000\127\000\044\000\157\000\075\000\111\000\076\000\036\000\
\044\000\110\000\116\000\077\000\118\000\046\000\137\000\017\000\
\016\000\018\000\079\000\087\000\081\000\014\000\028\000\124\000\
\126\000\044\000\028\000\014\000\028\000\028\000\019\000\028\000\
\028\000\028\000\028\000\092\000\161\000\136\000\064\000\067\000\
\020\000\021\000\022\000\020\000\021\000\022\000\145\000\028\000\
\064\000\067\000\060\000\093\000\148\000\149\000\044\000\151\000\
\044\000\028\000\044\000\050\000\014\000\163\000\154\000\098\000\
\050\000\078\000\040\000\057\000\159\000\040\000\114\000\112\000\
\162\000\040\000\040\000\040\000\040\000\068\000\040\000\040\000\
\040\000\040\000\041\000\044\000\100\000\041\000\050\000\044\000\
\129\000\041\000\041\000\041\000\041\000\131\000\041\000\041\000\
\041\000\041\000\133\000\072\000\140\000\069\000\005\000\141\000\
\040\000\040\000\063\000\142\000\007\000\008\000\143\000\009\000\
\010\000\011\000\012\000\150\000\073\000\102\000\103\000\005\000\
\041\000\041\000\156\000\065\000\158\000\007\000\008\000\044\000\
\009\000\010\000\011\000\012\000\160\000\050\000\050\000\082\000\
\045\000\013\000\005\000\115\000\121\000\044\000\063\000\138\000\
\007\000\008\000\083\000\009\000\010\000\011\000\012\000\001\000\
\002\000\003\000\013\000\016\000\000\000\050\000\022\000\016\000\
\000\000\016\000\022\000\044\000\022\000\000\000\000\000\005\000\
\000\000\005\000\019\000\000\000\019\000\013\000\000\000\000\000\
\016\000\016\000\000\000\022\000\022\000\016\000\044\000\000\000\
\022\000\005\000\016\000\019\000\019\000\022\000\016\000\000\000\
\019\000\022\000\005\000\000\000\016\000\019\000\007\000\022\000\
\007\000\019\000\084\000\006\000\005\000\006\000\010\000\019\000\
\010\000\008\000\009\000\008\000\009\000\057\000\058\000\007\000\
\007\000\057\000\058\000\057\000\058\000\057\000\058\000\059\000\
\000\000\007\000\000\000\059\000\000\000\059\000\006\000\059\000\
\000\000\010\000\000\000\007\000\008\000\009\000\000\000\117\000\
\006\000\119\000\000\000\010\000\000\000\000\000\008\000\009\000\
\094\000\000\000\017\000\000\000\095\000\000\000\007\000\008\000\
\000\000\009\000\010\000\011\000\012\000\000\000\005\000\000\000\
\035\000\019\000\065\000\066\000\007\000\008\000\000\000\009\000\
\010\000\011\000\012\000\020\000\021\000\022\000\113\000\000\000\
\017\000\000\000\095\000\013\000\007\000\008\000\000\000\009\000\
\010\000\011\000\012\000\000\000\005\000\000\000\035\000\019\000\
\027\000\013\000\007\000\008\000\000\000\009\000\010\000\011\000\
\012\000\020\000\021\000\022\000\035\000\028\000\029\000\000\000\
\000\000\013\000\005\000\030\000\031\000\000\000\027\000\000\000\
\007\000\008\000\000\000\009\000\010\000\011\000\012\000\013\000\
\000\000\000\000\000\000\028\000\029\000\000\000\000\000\005\000\
\000\000\030\000\031\000\063\000\000\000\007\000\008\000\000\000\
\009\000\010\000\011\000\012\000\000\000\013\000\000\000\000\000\
\005\000\000\000\060\000\000\000\063\000\146\000\007\000\008\000\
\044\000\009\000\010\000\011\000\012\000\000\000\000\000\000\000\
\000\000\005\000\013\000\000\000\000\000\063\000\000\000\007\000\
\008\000\044\000\009\000\010\000\011\000\012\000\000\000\000\000\
\000\000\000\000\005\000\013\000\000\000\000\000\065\000\139\000\
\007\000\008\000\044\000\009\000\010\000\011\000\012\000\000\000\
\000\000\005\000\000\000\000\000\013\000\065\000\147\000\007\000\
\008\000\000\000\009\000\010\000\011\000\012\000\000\000\000\000\
\005\000\000\000\000\000\000\000\006\000\013\000\007\000\008\000\
\000\000\009\000\010\000\011\000\012\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\013\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\013\000"

let yycheck = "\003\001\
\000\000\000\000\000\000\000\000\027\000\009\001\013\000\003\001\
\000\000\007\001\007\001\000\000\024\001\025\001\004\001\003\001\
\005\001\001\000\008\001\002\000\010\001\011\001\006\000\013\001\
\014\001\015\001\016\001\011\000\012\000\013\000\020\001\029\001\
\029\001\017\001\057\000\058\000\059\000\000\000\042\001\000\000\
\029\001\029\001\038\001\027\000\000\000\029\001\069\000\000\000\
\071\000\039\001\000\000\000\000\036\000\037\000\004\001\007\001\
\040\000\041\000\004\001\043\001\006\001\004\001\008\001\086\000\
\003\001\072\000\073\000\050\000\004\001\053\000\020\001\042\001\
\003\001\007\001\007\001\021\001\060\000\029\001\004\001\063\000\
\063\000\065\000\065\000\004\001\007\001\031\001\032\001\033\001\
\072\000\073\000\029\001\024\001\025\001\076\000\077\000\029\001\
\079\000\120\000\029\001\122\000\123\000\034\001\085\000\040\001\
\087\000\112\000\029\001\007\001\002\001\092\000\005\001\095\000\
\029\001\030\001\098\000\005\001\100\000\004\001\125\000\006\001\
\004\001\008\001\029\001\005\001\008\001\003\001\004\001\110\000\
\112\000\029\001\008\001\009\001\010\001\011\001\021\001\013\001\
\014\001\015\001\016\001\005\001\007\001\125\000\126\000\127\000\
\031\001\032\001\033\001\031\001\032\001\033\001\133\000\029\001\
\136\000\137\000\023\001\004\001\140\000\141\000\029\001\143\000\
\029\001\039\001\029\001\003\001\042\001\007\001\150\000\006\001\
\003\001\009\001\001\001\024\001\156\000\004\001\009\001\029\001\
\160\000\008\001\009\001\010\001\011\001\019\001\013\001\014\001\
\015\001\016\001\001\001\029\001\006\001\004\001\003\001\029\001\
\019\001\008\001\009\001\010\001\011\001\017\001\013\001\014\001\
\015\001\016\001\003\001\001\001\006\001\043\001\004\001\006\001\
\039\001\040\001\008\001\018\001\010\001\011\001\006\001\013\001\
\014\001\015\001\016\001\006\001\001\001\072\000\073\000\004\001\
\039\001\040\001\006\001\008\001\018\001\010\001\011\001\029\001\
\013\001\014\001\015\001\016\001\006\001\003\001\003\001\051\000\
\040\001\039\001\004\001\009\001\009\001\040\001\008\001\009\001\
\010\001\011\001\051\000\013\001\014\001\015\001\016\001\001\000\
\002\000\003\000\039\001\003\001\255\255\003\001\003\001\007\001\
\255\255\009\001\007\001\029\001\009\001\255\255\255\255\007\001\
\255\255\009\001\007\001\255\255\009\001\039\001\255\255\255\255\
\024\001\025\001\255\255\024\001\025\001\029\001\029\001\255\255\
\029\001\025\001\034\001\024\001\025\001\034\001\038\001\255\255\
\029\001\038\001\034\001\255\255\044\001\034\001\007\001\044\001\
\009\001\038\001\009\001\007\001\044\001\009\001\007\001\044\001\
\009\001\007\001\007\001\009\001\009\001\024\001\025\001\024\001\
\025\001\024\001\025\001\024\001\025\001\024\001\025\001\034\001\
\255\255\034\001\255\255\034\001\255\255\034\001\034\001\034\001\
\255\255\034\001\255\255\044\001\034\001\034\001\255\255\044\001\
\044\001\044\001\255\255\044\001\255\255\255\255\044\001\044\001\
\004\001\255\255\006\001\255\255\008\001\255\255\010\001\011\001\
\255\255\013\001\014\001\015\001\016\001\255\255\004\001\255\255\
\020\001\021\001\008\001\009\001\010\001\011\001\255\255\013\001\
\014\001\015\001\016\001\031\001\032\001\033\001\004\001\255\255\
\006\001\255\255\008\001\039\001\010\001\011\001\255\255\013\001\
\014\001\015\001\016\001\255\255\004\001\255\255\020\001\021\001\
\008\001\039\001\010\001\011\001\255\255\013\001\014\001\015\001\
\016\001\031\001\032\001\033\001\020\001\021\001\022\001\255\255\
\255\255\039\001\004\001\027\001\028\001\255\255\008\001\255\255\
\010\001\011\001\255\255\013\001\014\001\015\001\016\001\039\001\
\255\255\255\255\255\255\021\001\022\001\255\255\255\255\004\001\
\255\255\027\001\028\001\008\001\255\255\010\001\011\001\255\255\
\013\001\014\001\015\001\016\001\255\255\039\001\255\255\255\255\
\004\001\255\255\023\001\255\255\008\001\009\001\010\001\011\001\
\029\001\013\001\014\001\015\001\016\001\255\255\255\255\255\255\
\255\255\004\001\039\001\255\255\255\255\008\001\255\255\010\001\
\011\001\029\001\013\001\014\001\015\001\016\001\255\255\255\255\
\255\255\255\255\004\001\039\001\255\255\255\255\008\001\009\001\
\010\001\011\001\029\001\013\001\014\001\015\001\016\001\255\255\
\255\255\004\001\255\255\255\255\039\001\008\001\009\001\010\001\
\011\001\255\255\013\001\014\001\015\001\016\001\255\255\255\255\
\004\001\255\255\255\255\255\255\008\001\039\001\010\001\011\001\
\255\255\013\001\014\001\015\001\016\001\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\039\001\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\039\001"

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
# 52 "lambdaAst.mly"
      ( Top )
# 402 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    Obj.repr(
# 53 "lambdaAst.mly"
      ( Bot )
# 408 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'prop_grammar) in
    Obj.repr(
# 54 "lambdaAst.mly"
                             ( _2 )
# 415 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'prop_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'prop_grammar) in
    Obj.repr(
# 55 "lambdaAst.mly"
                                     ( Conjunction (_1, _3) )
# 423 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'prop_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'prop_grammar) in
    Obj.repr(
# 56 "lambdaAst.mly"
                                    ( Disjunction (_1, _3) )
# 431 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'prop_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'prop_grammar) in
    Obj.repr(
# 57 "lambdaAst.mly"
                                                         ( Implication (_1, _3) )
# 439 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : 'term_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'term_grammar) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'type_grammar) in
    Obj.repr(
# 58 "lambdaAst.mly"
                                                      ( Eq (_1, _3, _5) )
# 448 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'type_grammar) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'prop_grammar) in
    Obj.repr(
# 59 "lambdaAst.mly"
                                                                     ( Forall (_2, _4, _6) )
# 457 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'type_grammar) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'prop_grammar) in
    Obj.repr(
# 60 "lambdaAst.mly"
                                                                     ( Exists (_2, _4, _6) )
# 466 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'prop_grammar) in
    Obj.repr(
# 61 "lambdaAst.mly"
                                                 ( ForallGen (_2, _4) )
# 474 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    Obj.repr(
# 63 "lambdaAst.mly"
       ( Bool )
# 480 "lambdaAst.ml"
               : 'atom_type_grammar))
; (fun __caml_parser_env ->
    Obj.repr(
# 64 "lambdaAst.mly"
       ( Unit )
# 486 "lambdaAst.ml"
               : 'atom_type_grammar))
; (fun __caml_parser_env ->
    Obj.repr(
# 65 "lambdaAst.mly"
      ( Nat )
# 492 "lambdaAst.ml"
               : 'atom_type_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 66 "lambdaAst.mly"
      ( TVar _1 )
# 499 "lambdaAst.ml"
               : 'atom_type_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'type_grammar) in
    Obj.repr(
# 67 "lambdaAst.mly"
                             ( _2 )
# 506 "lambdaAst.ml"
               : 'atom_type_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'atom_type_grammar) in
    Obj.repr(
# 69 "lambdaAst.mly"
                    ( _1 )
# 513 "lambdaAst.ml"
               : 'type_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'type_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'type_grammar) in
    Obj.repr(
# 70 "lambdaAst.mly"
                                                   ( Map ("_", _1, _3) )
# 521 "lambdaAst.ml"
               : 'type_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : 'type_grammar) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'type_grammar) in
    Obj.repr(
# 71 "lambdaAst.mly"
                                                                          ( Map (_2, _4, _7) )
# 530 "lambdaAst.ml"
               : 'type_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'type_grammar) in
    Obj.repr(
# 72 "lambdaAst.mly"
                                                 ( Gen (_2, _4) )
# 538 "lambdaAst.ml"
               : 'type_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : 'type_grammar) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'prop_grammar) in
    Obj.repr(
# 73 "lambdaAst.mly"
                                                                            ( Refine (_2, _4, _6) )
# 547 "lambdaAst.ml"
               : 'type_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'prod_type) in
    Obj.repr(
# 74 "lambdaAst.mly"
                       ( Prod _1 )
# 554 "lambdaAst.ml"
               : 'type_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'atom_type_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'atom_type_grammar) in
    Obj.repr(
# 76 "lambdaAst.mly"
                                           ( [_1; _3] )
# 562 "lambdaAst.ml"
               : 'prod_type))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'atom_type_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'prod_type) in
    Obj.repr(
# 77 "lambdaAst.mly"
                                   ( _1 :: _3 )
# 570 "lambdaAst.ml"
               : 'prod_type))
; (fun __caml_parser_env ->
    Obj.repr(
# 79 "lambdaAst.mly"
       ( NatO )
# 576 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    Obj.repr(
# 80 "lambdaAst.mly"
       ( NatSucc )
# 582 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    Obj.repr(
# 81 "lambdaAst.mly"
        ( False )
# 588 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    Obj.repr(
# 82 "lambdaAst.mly"
       ( True )
# 594 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 83 "lambdaAst.mly"
      ( Var _1 )
# 601 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'app_term_grammar) in
    Obj.repr(
# 84 "lambdaAst.mly"
                                 ( _2 )
# 608 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 3 : 'type_grammar) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'app_term_grammar) in
    Obj.repr(
# 85 "lambdaAst.mly"
                                                                   ( Abs (_3, _5, _7) )
# 617 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 3 : 'type_grammar) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'term_grammar) in
    Obj.repr(
# 86 "lambdaAst.mly"
                                                               ( Abs (_3, _5, _7) )
# 626 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _4 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'app_term_grammar) in
    Obj.repr(
# 87 "lambdaAst.mly"
                                                     ( Generic (_4, _6) )
# 634 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _4 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'term_grammar) in
    Obj.repr(
# 88 "lambdaAst.mly"
                                                 ( Generic (_4, _6) )
# 642 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'term_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 89 "lambdaAst.mly"
                       ( Proj (_1, _3) )
# 650 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'term_list) in
    Obj.repr(
# 90 "lambdaAst.mly"
                    ( Tuple _2 )
# 657 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 11 : 'term_grammar) in
    let _4 = (Parsing.peek_val __caml_parser_env 9 : 'prop_grammar) in
    let _8 = (Parsing.peek_val __caml_parser_env 5 : 'term_grammar) in
    let _12 = (Parsing.peek_val __caml_parser_env 1 : 'term_grammar) in
    Obj.repr(
# 91 "lambdaAst.mly"
                                                                                                             ( Ite (_2, _8, _12, _4) )
# 667 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 10 : 'term_grammar) in
    let _4 = (Parsing.peek_val __caml_parser_env 8 : 'prop_grammar) in
    let _8 = (Parsing.peek_val __caml_parser_env 4 : 'term_grammar) in
    let _11 = (Parsing.peek_val __caml_parser_env 1 : 'term_grammar) in
    Obj.repr(
# 92 "lambdaAst.mly"
                                                                                                       ( For (_2, _8, _11, _4) )
# 677 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 8 : 'term_grammar) in
    let _5 = (Parsing.peek_val __caml_parser_env 5 : 'term_grammar) in
    let _9 = (Parsing.peek_val __caml_parser_env 1 : 'term_grammar) in
    Obj.repr(
# 93 "lambdaAst.mly"
                                                                                  ( Ite (_2, _5, _9, Top) )
# 686 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 7 : 'term_grammar) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : 'term_grammar) in
    let _8 = (Parsing.peek_val __caml_parser_env 1 : 'term_grammar) in
    Obj.repr(
# 94 "lambdaAst.mly"
                                                                            ( For (_2, _5, _8, Top) )
# 695 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'term_grammar) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'term_grammar) in
    Obj.repr(
# 96 "lambdaAst.mly"
                                      ( App (_1, _2) )
# 703 "lambdaAst.ml"
               : 'app_term_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'app_term_grammar) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'term_grammar) in
    Obj.repr(
# 97 "lambdaAst.mly"
                                          ( App (_1, _2) )
# 711 "lambdaAst.ml"
               : 'app_term_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'app_term_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'type_grammar) in
    Obj.repr(
# 98 "lambdaAst.mly"
                                                        ( TApp (_1, _3) )
# 719 "lambdaAst.ml"
               : 'app_term_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'term_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'type_grammar) in
    Obj.repr(
# 99 "lambdaAst.mly"
                                                    ( TApp (_1, _3) )
# 727 "lambdaAst.ml"
               : 'app_term_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'app_term_grammar) in
    Obj.repr(
# 101 "lambdaAst.mly"
                   ( [_1] )
# 734 "lambdaAst.ml"
               : 'term_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'term_grammar) in
    Obj.repr(
# 102 "lambdaAst.mly"
               ( [_1] )
# 741 "lambdaAst.ml"
               : 'term_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'app_term_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'term_list) in
    Obj.repr(
# 103 "lambdaAst.mly"
                                   ( _1 :: _3 )
# 749 "lambdaAst.ml"
               : 'term_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'term_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'term_list) in
    Obj.repr(
# 104 "lambdaAst.mly"
                               ( _1 :: _3 )
# 757 "lambdaAst.ml"
               : 'term_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'term_grammar) in
    Obj.repr(
# 106 "lambdaAst.mly"
                   ( _1 )
# 764 "lambdaAst.ml"
               : PreIr.term_ast))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'type_grammar) in
    Obj.repr(
# 108 "lambdaAst.mly"
                   ( _1 )
# 771 "lambdaAst.ml"
               : PreIr.type_ast))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'prop_grammar) in
    Obj.repr(
# 110 "lambdaAst.mly"
                   ( _1 )
# 778 "lambdaAst.ml"
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
