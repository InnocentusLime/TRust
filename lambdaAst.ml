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
  | PROD
  | LANGLE
  | RANGLE

open Parsing;;
let _ = parse_error;;
# 2 "lambdaAst.mly"
open PreIr;;
# 52 "lambdaAst.ml"
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
  297 (* PROD *);
  298 (* LANGLE *);
  299 (* RANGLE *);
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
\005\000\005\000\005\000\005\000\005\000\010\000\010\000\010\000\
\010\000\010\000\010\000\009\000\009\000\009\000\009\000\011\000\
\011\000\011\000\011\000\001\000\002\000\003\000\000\000\000\000\
\000\000"

let yylen = "\002\000\
\001\000\001\000\003\000\003\000\003\000\003\000\005\000\006\000\
\006\000\004\000\001\000\001\000\001\000\001\000\003\000\001\000\
\003\000\007\000\004\000\007\000\001\000\003\000\003\000\001\000\
\001\000\001\000\001\000\001\000\001\000\003\000\003\000\003\000\
\003\000\013\000\012\000\010\000\009\000\006\000\006\000\005\000\
\005\000\006\000\005\000\002\000\002\000\004\000\004\000\001\000\
\001\000\003\000\003\000\002\000\002\000\002\000\002\000\002\000\
\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\029\000\000\000\025\000\026\000\
\024\000\028\000\027\000\000\000\000\000\000\000\055\000\000\000\
\014\000\000\000\000\000\000\000\012\000\011\000\013\000\056\000\
\000\000\000\000\021\000\000\000\000\000\000\000\001\000\002\000\
\057\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\052\000\000\000\000\000\000\000\
\000\000\000\000\053\000\000\000\000\000\000\000\000\000\000\000\
\000\000\054\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\030\000\000\000\031\000\000\000\000\000\
\000\000\000\000\000\000\000\000\033\000\032\000\000\000\000\000\
\015\000\000\000\017\000\000\000\000\000\023\000\003\000\000\000\
\000\000\000\000\004\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\051\000\050\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\047\000\046\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\043\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\042\000\000\000\000\000\
\000\000\000\000\020\000\018\000\000\000\000\000\000\000\000\000\
\037\000\000\000\000\000\000\000\000\000\036\000\000\000\000\000\
\000\000\035\000\000\000\034\000"

let yydgoto = "\004\000\
\015\000\024\000\033\000\034\000\035\000\049\000\026\000\027\000\
\038\000\039\000\044\000"

let yysindex = "\178\000\
\006\001\020\255\163\000\000\000\000\000\204\000\000\000\000\000\
\000\000\000\000\000\000\006\001\006\001\006\001\000\000\005\000\
\000\000\013\255\121\255\033\255\000\000\000\000\000\000\000\000\
\002\000\225\254\000\000\141\000\038\255\059\255\000\000\000\000\
\000\000\036\000\252\254\096\255\217\000\249\000\057\255\028\255\
\032\255\216\255\084\000\238\254\000\000\066\255\075\255\090\255\
\018\255\095\255\000\000\020\255\140\255\053\255\184\000\027\255\
\130\255\000\000\163\000\163\000\163\000\006\001\134\255\122\255\
\097\000\127\255\097\000\000\000\127\255\000\000\163\255\163\000\
\171\255\163\000\006\001\006\001\000\000\000\000\020\255\020\255\
\000\000\020\255\000\000\020\255\225\254\000\000\000\000\020\255\
\163\000\020\255\000\000\143\255\106\255\172\255\020\255\160\255\
\000\000\127\000\161\255\173\255\006\001\141\255\006\001\209\255\
\000\000\000\000\010\255\210\255\200\255\006\255\125\255\011\255\
\020\255\017\255\204\000\090\255\000\000\000\000\060\255\197\255\
\062\255\201\255\163\000\220\255\163\000\163\000\200\255\204\000\
\217\000\023\001\000\000\230\255\232\255\221\255\234\255\009\255\
\020\255\125\255\125\255\217\000\023\001\000\000\006\001\006\001\
\235\255\006\001\000\000\000\000\068\255\069\255\006\001\074\255\
\000\000\236\255\076\255\226\255\006\001\000\000\240\255\126\255\
\006\001\000\000\133\255\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\207\255\208\255\000\000\000\000\000\000\000\000\253\254\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\098\255\000\000\000\000\182\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\004\000\000\000\000\000\000\000\
\000\000\000\000\000\000\015\000\044\000\000\000\000\000\000\000\
\196\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\007\000\000\000\011\000\000\000\
\000\000\000\000\000\000\196\255\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\039\000\000\000\
\241\255\242\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\012\000\050\000\244\255\247\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\000\000\000\000\062\000\017\000\006\000\196\000\201\000\
\245\255\013\000\139\000"

let yytablesize = 574
let yytable = "\014\000\
\016\000\051\000\043\000\022\000\045\000\014\000\019\000\025\000\
\052\000\053\000\010\000\008\000\052\000\052\000\005\000\147\000\
\047\000\016\000\062\000\052\000\052\000\077\000\037\000\017\000\
\046\000\018\000\081\000\019\000\040\000\041\000\042\000\088\000\
\059\000\060\000\125\000\058\000\050\000\014\000\007\000\126\000\
\020\000\056\000\061\000\006\000\055\000\128\000\071\000\123\000\
\073\000\009\000\021\000\022\000\023\000\066\000\069\000\089\000\
\046\000\083\000\066\000\069\000\046\000\087\000\057\000\043\000\
\043\000\070\000\132\000\078\000\134\000\072\000\099\000\066\000\
\100\000\074\000\153\000\154\000\059\000\060\000\094\000\079\000\
\156\000\037\000\158\000\037\000\107\000\108\000\061\000\109\000\
\046\000\054\000\046\000\042\000\042\000\110\000\080\000\112\000\
\046\000\046\000\044\000\063\000\114\000\044\000\046\000\130\000\
\046\000\044\000\044\000\044\000\044\000\044\000\044\000\044\000\
\044\000\044\000\037\000\064\000\141\000\119\000\127\000\121\000\
\091\000\092\000\093\000\082\000\048\000\096\000\018\000\131\000\
\019\000\059\000\060\000\129\000\162\000\102\000\090\000\104\000\
\044\000\044\000\095\000\164\000\142\000\020\000\148\000\017\000\
\140\000\066\000\069\000\084\000\059\000\060\000\111\000\021\000\
\022\000\023\000\046\000\046\000\066\000\069\000\061\000\149\000\
\150\000\046\000\152\000\052\000\059\000\060\000\059\000\155\000\
\101\000\117\000\021\000\022\000\023\000\160\000\061\000\052\000\
\103\000\163\000\001\000\002\000\003\000\118\000\045\000\120\000\
\136\000\045\000\138\000\139\000\115\000\045\000\045\000\045\000\
\045\000\045\000\045\000\045\000\045\000\045\000\014\000\029\000\
\046\000\113\000\052\000\029\000\014\000\029\000\029\000\029\000\
\029\000\029\000\029\000\029\000\052\000\105\000\106\000\133\000\
\075\000\135\000\124\000\005\000\045\000\045\000\137\000\065\000\
\029\000\007\000\008\000\009\000\010\000\011\000\012\000\013\000\
\059\000\060\000\029\000\143\000\014\000\144\000\145\000\146\000\
\151\000\157\000\061\000\159\000\046\000\161\000\049\000\048\000\
\085\000\041\000\040\000\122\000\039\000\086\000\014\000\038\000\
\000\000\000\000\000\000\016\000\052\000\000\000\022\000\016\000\
\000\000\016\000\022\000\000\000\022\000\019\000\000\000\019\000\
\000\000\010\000\008\000\010\000\008\000\005\000\000\000\005\000\
\016\000\016\000\000\000\022\000\022\000\016\000\019\000\019\000\
\022\000\046\000\016\000\019\000\000\000\022\000\016\000\005\000\
\019\000\022\000\000\000\016\000\019\000\007\000\022\000\007\000\
\005\000\019\000\006\000\000\000\006\000\010\000\008\000\000\000\
\009\000\005\000\009\000\059\000\060\000\000\000\007\000\007\000\
\000\000\000\000\000\000\000\000\000\000\061\000\000\000\000\000\
\007\000\000\000\000\000\000\000\000\000\006\000\000\000\000\000\
\000\000\007\000\000\000\000\000\076\000\000\000\006\000\005\000\
\000\000\000\000\000\000\067\000\009\000\007\000\008\000\009\000\
\010\000\011\000\012\000\013\000\097\000\000\000\018\000\000\000\
\098\000\000\000\007\000\008\000\009\000\010\000\011\000\012\000\
\013\000\000\000\000\000\000\000\036\000\020\000\000\000\000\000\
\000\000\000\000\014\000\000\000\000\000\000\000\000\000\021\000\
\022\000\023\000\116\000\000\000\018\000\000\000\098\000\014\000\
\007\000\008\000\009\000\010\000\011\000\012\000\013\000\000\000\
\005\000\000\000\036\000\020\000\028\000\000\000\007\000\008\000\
\009\000\010\000\011\000\012\000\013\000\021\000\022\000\023\000\
\036\000\029\000\030\000\000\000\000\000\014\000\005\000\031\000\
\032\000\000\000\028\000\000\000\007\000\008\000\009\000\010\000\
\011\000\012\000\013\000\014\000\000\000\000\000\000\000\029\000\
\030\000\000\000\000\000\005\000\000\000\031\000\032\000\065\000\
\000\000\007\000\008\000\009\000\010\000\011\000\012\000\013\000\
\000\000\014\000\000\000\000\000\000\000\000\000\062\000\005\000\
\000\000\000\000\000\000\006\000\046\000\007\000\008\000\009\000\
\010\000\011\000\012\000\013\000\005\000\000\000\014\000\036\000\
\065\000\000\000\007\000\008\000\009\000\010\000\011\000\012\000\
\013\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\014\000\000\000\000\000\046\000\000\000\000\000\
\000\000\000\000\000\000\000\000\005\000\000\000\000\000\014\000\
\067\000\068\000\007\000\008\000\009\000\010\000\011\000\012\000\
\013\000\005\000\000\000\000\000\000\000\006\000\000\000\007\000\
\008\000\009\000\010\000\011\000\012\000\013\000\000\000\000\000\
\000\000\000\000\005\000\000\000\000\000\000\000\067\000\014\000\
\007\000\008\000\009\000\010\000\011\000\012\000\013\000\000\000\
\000\000\000\000\000\000\000\000\014\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\014\000"

let yycheck = "\003\001\
\000\000\000\000\014\000\000\000\000\000\009\001\000\000\002\000\
\003\001\041\001\000\000\000\000\003\001\003\001\000\000\007\001\
\004\001\001\000\023\001\003\001\003\001\040\001\006\000\004\001\
\029\001\006\001\009\001\008\001\012\000\013\000\014\000\005\001\
\024\001\025\001\029\001\000\000\004\001\041\001\000\000\029\001\
\021\001\004\001\034\001\000\000\028\000\029\001\019\001\038\001\
\017\001\000\000\031\001\032\001\033\001\037\000\038\000\029\001\
\029\001\052\000\042\000\043\000\029\001\009\001\004\001\075\000\
\076\000\009\001\007\001\002\001\007\001\042\001\065\000\055\000\
\067\000\042\001\007\001\007\001\024\001\025\001\062\000\005\001\
\007\001\065\000\007\001\067\000\079\000\080\000\034\001\082\000\
\029\001\028\000\029\001\075\000\076\000\088\000\005\001\090\000\
\029\001\029\001\001\001\004\001\095\000\004\001\029\001\115\000\
\029\001\008\001\009\001\010\001\011\001\012\001\013\001\014\001\
\015\001\016\001\098\000\020\001\128\000\101\000\113\000\103\000\
\059\000\060\000\061\000\029\001\004\001\004\001\006\001\115\000\
\008\001\024\001\025\001\115\000\007\001\072\000\005\001\074\000\
\039\001\040\001\005\001\007\001\128\000\021\001\137\000\004\001\
\128\000\129\000\130\000\008\001\024\001\025\001\089\000\031\001\
\032\001\033\001\029\001\029\001\140\000\141\000\034\001\143\000\
\144\000\029\001\146\000\003\001\024\001\025\001\024\001\151\000\
\006\001\009\001\031\001\032\001\033\001\157\000\034\001\003\001\
\006\001\161\000\001\000\002\000\003\000\009\001\001\001\043\001\
\123\000\004\001\125\000\126\000\029\001\008\001\009\001\010\001\
\011\001\012\001\013\001\014\001\015\001\016\001\003\001\004\001\
\029\001\030\001\003\001\008\001\009\001\010\001\011\001\012\001\
\013\001\014\001\015\001\016\001\003\001\075\000\076\000\019\001\
\001\001\017\001\009\001\004\001\039\001\040\001\003\001\008\001\
\029\001\010\001\011\001\012\001\013\001\014\001\015\001\016\001\
\024\001\025\001\039\001\006\001\041\001\006\001\018\001\006\001\
\006\001\006\001\034\001\018\001\029\001\006\001\040\001\040\001\
\053\000\009\001\009\001\043\001\009\001\053\000\039\001\009\001\
\255\255\255\255\255\255\003\001\003\001\255\255\003\001\007\001\
\255\255\009\001\007\001\255\255\009\001\007\001\255\255\009\001\
\255\255\007\001\007\001\009\001\009\001\007\001\255\255\009\001\
\024\001\025\001\255\255\024\001\025\001\029\001\024\001\025\001\
\029\001\029\001\034\001\029\001\255\255\034\001\038\001\025\001\
\034\001\038\001\255\255\043\001\038\001\007\001\043\001\009\001\
\034\001\043\001\007\001\255\255\009\001\043\001\043\001\255\255\
\007\001\043\001\009\001\024\001\025\001\255\255\024\001\025\001\
\255\255\255\255\255\255\255\255\255\255\034\001\255\255\255\255\
\034\001\255\255\255\255\255\255\255\255\034\001\255\255\255\255\
\255\255\043\001\255\255\255\255\001\001\255\255\043\001\004\001\
\255\255\255\255\255\255\008\001\043\001\010\001\011\001\012\001\
\013\001\014\001\015\001\016\001\004\001\255\255\006\001\255\255\
\008\001\255\255\010\001\011\001\012\001\013\001\014\001\015\001\
\016\001\255\255\255\255\255\255\020\001\021\001\255\255\255\255\
\255\255\255\255\039\001\255\255\255\255\255\255\255\255\031\001\
\032\001\033\001\004\001\255\255\006\001\255\255\008\001\039\001\
\010\001\011\001\012\001\013\001\014\001\015\001\016\001\255\255\
\004\001\255\255\020\001\021\001\008\001\255\255\010\001\011\001\
\012\001\013\001\014\001\015\001\016\001\031\001\032\001\033\001\
\020\001\021\001\022\001\255\255\255\255\039\001\004\001\027\001\
\028\001\255\255\008\001\255\255\010\001\011\001\012\001\013\001\
\014\001\015\001\016\001\039\001\255\255\255\255\255\255\021\001\
\022\001\255\255\255\255\004\001\255\255\027\001\028\001\008\001\
\255\255\010\001\011\001\012\001\013\001\014\001\015\001\016\001\
\255\255\039\001\255\255\255\255\255\255\255\255\023\001\004\001\
\255\255\255\255\255\255\008\001\029\001\010\001\011\001\012\001\
\013\001\014\001\015\001\016\001\004\001\255\255\039\001\020\001\
\008\001\255\255\010\001\011\001\012\001\013\001\014\001\015\001\
\016\001\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\039\001\255\255\255\255\029\001\255\255\255\255\
\255\255\255\255\255\255\255\255\004\001\255\255\255\255\039\001\
\008\001\009\001\010\001\011\001\012\001\013\001\014\001\015\001\
\016\001\004\001\255\255\255\255\255\255\008\001\255\255\010\001\
\011\001\012\001\013\001\014\001\015\001\016\001\255\255\255\255\
\255\255\255\255\004\001\255\255\255\255\255\255\008\001\039\001\
\010\001\011\001\012\001\013\001\014\001\015\001\016\001\255\255\
\255\255\255\255\255\255\255\255\039\001\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\039\001"

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
# 51 "lambdaAst.mly"
      ( Top )
# 405 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    Obj.repr(
# 52 "lambdaAst.mly"
      ( Bot )
# 411 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'prop_grammar) in
    Obj.repr(
# 53 "lambdaAst.mly"
                             ( _2 )
# 418 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'prop_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'prop_grammar) in
    Obj.repr(
# 54 "lambdaAst.mly"
                                     ( Conjunction (_1, _3) )
# 426 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'prop_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'prop_grammar) in
    Obj.repr(
# 55 "lambdaAst.mly"
                                    ( Disjunction (_1, _3) )
# 434 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'prop_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'prop_grammar) in
    Obj.repr(
# 56 "lambdaAst.mly"
                                                         ( Implication (_1, _3) )
# 442 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : 'term_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'term_grammar) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'type_grammar) in
    Obj.repr(
# 57 "lambdaAst.mly"
                                                      ( Eq (_1, _3, _5) )
# 451 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'type_grammar) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'prop_grammar) in
    Obj.repr(
# 58 "lambdaAst.mly"
                                                                 ( Forall (_2, _4, _6) )
# 460 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'type_grammar) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'prop_grammar) in
    Obj.repr(
# 59 "lambdaAst.mly"
                                                                 ( Exists (_2, _4, _6) )
# 469 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'prop_grammar) in
    Obj.repr(
# 60 "lambdaAst.mly"
                                             ( ForallGen (_2, _4) )
# 477 "lambdaAst.ml"
               : 'prop_grammar))
; (fun __caml_parser_env ->
    Obj.repr(
# 62 "lambdaAst.mly"
       ( Bool )
# 483 "lambdaAst.ml"
               : 'atom_type_grammar))
; (fun __caml_parser_env ->
    Obj.repr(
# 63 "lambdaAst.mly"
       ( Unit )
# 489 "lambdaAst.ml"
               : 'atom_type_grammar))
; (fun __caml_parser_env ->
    Obj.repr(
# 64 "lambdaAst.mly"
      ( Nat )
# 495 "lambdaAst.ml"
               : 'atom_type_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 65 "lambdaAst.mly"
      ( TVar _1 )
# 502 "lambdaAst.ml"
               : 'atom_type_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'type_grammar) in
    Obj.repr(
# 66 "lambdaAst.mly"
                             ( _2 )
# 509 "lambdaAst.ml"
               : 'atom_type_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'atom_type_grammar) in
    Obj.repr(
# 68 "lambdaAst.mly"
                    ( _1 )
# 516 "lambdaAst.ml"
               : 'type_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'type_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'type_grammar) in
    Obj.repr(
# 69 "lambdaAst.mly"
                                                   ( Map ("_", _1, _3) )
# 524 "lambdaAst.ml"
               : 'type_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : 'type_grammar) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'type_grammar) in
    Obj.repr(
# 70 "lambdaAst.mly"
                                                                          ( Map (_2, _4, _7) )
# 533 "lambdaAst.ml"
               : 'type_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'type_grammar) in
    Obj.repr(
# 71 "lambdaAst.mly"
                                                 ( Gen (_2, _4) )
# 541 "lambdaAst.ml"
               : 'type_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : 'type_grammar) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'prop_grammar) in
    Obj.repr(
# 72 "lambdaAst.mly"
                                                                            ( Refine (_2, _4, _6) )
# 550 "lambdaAst.ml"
               : 'type_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'prod_type) in
    Obj.repr(
# 73 "lambdaAst.mly"
                       ( Prod _1 )
# 557 "lambdaAst.ml"
               : 'type_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'atom_type_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'atom_type_grammar) in
    Obj.repr(
# 75 "lambdaAst.mly"
                                           ( [_1; _3] )
# 565 "lambdaAst.ml"
               : 'prod_type))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'atom_type_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'prod_type) in
    Obj.repr(
# 76 "lambdaAst.mly"
                                   ( _1 :: _3 )
# 573 "lambdaAst.ml"
               : 'prod_type))
; (fun __caml_parser_env ->
    Obj.repr(
# 78 "lambdaAst.mly"
      ( Nil )
# 579 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    Obj.repr(
# 79 "lambdaAst.mly"
       ( NatO )
# 585 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    Obj.repr(
# 80 "lambdaAst.mly"
       ( NatSucc )
# 591 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    Obj.repr(
# 81 "lambdaAst.mly"
        ( False )
# 597 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    Obj.repr(
# 82 "lambdaAst.mly"
       ( True )
# 603 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 83 "lambdaAst.mly"
      ( Var _1 )
# 610 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'app_term_grammar) in
    Obj.repr(
# 84 "lambdaAst.mly"
                                 ( _2 )
# 617 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'abs_term_grammar) in
    Obj.repr(
# 85 "lambdaAst.mly"
                                 ( _2 )
# 624 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'term_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 86 "lambdaAst.mly"
                       ( Proj (_1, _3) )
# 632 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'term_list) in
    Obj.repr(
# 87 "lambdaAst.mly"
                    ( Tuple _2 )
# 639 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 11 : 'term_grammar) in
    let _4 = (Parsing.peek_val __caml_parser_env 9 : 'prop_grammar) in
    let _8 = (Parsing.peek_val __caml_parser_env 5 : 'term_grammar) in
    let _12 = (Parsing.peek_val __caml_parser_env 1 : 'term_grammar) in
    Obj.repr(
# 88 "lambdaAst.mly"
                                                                                                             ( Ite (_2, _8, _12, _4) )
# 649 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 10 : 'term_grammar) in
    let _4 = (Parsing.peek_val __caml_parser_env 8 : 'prop_grammar) in
    let _8 = (Parsing.peek_val __caml_parser_env 4 : 'term_grammar) in
    let _11 = (Parsing.peek_val __caml_parser_env 1 : 'term_grammar) in
    Obj.repr(
# 89 "lambdaAst.mly"
                                                                                                       ( For (_2, _8, _11, _4) )
# 659 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 8 : 'term_grammar) in
    let _5 = (Parsing.peek_val __caml_parser_env 5 : 'term_grammar) in
    let _9 = (Parsing.peek_val __caml_parser_env 1 : 'term_grammar) in
    Obj.repr(
# 90 "lambdaAst.mly"
                                                                                  ( Ite (_2, _5, _9, Top) )
# 668 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 7 : 'term_grammar) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : 'term_grammar) in
    let _8 = (Parsing.peek_val __caml_parser_env 1 : 'term_grammar) in
    Obj.repr(
# 91 "lambdaAst.mly"
                                                                            ( For (_2, _5, _8, Top) )
# 677 "lambdaAst.ml"
               : 'term_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'type_grammar) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'app_term_grammar) in
    Obj.repr(
# 93 "lambdaAst.mly"
                                                     ( Abs (_2, _4, _6) )
# 686 "lambdaAst.ml"
               : 'abs_term_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'type_grammar) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'term_grammar) in
    Obj.repr(
# 94 "lambdaAst.mly"
                                                 ( Abs (_2, _4, _6) )
# 695 "lambdaAst.ml"
               : 'abs_term_grammar))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'app_term_grammar) in
    Obj.repr(
# 95 "lambdaAst.mly"
                                       ( Generic (_3, _5) )
# 703 "lambdaAst.ml"
               : 'abs_term_grammar))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'term_grammar) in
    Obj.repr(
# 96 "lambdaAst.mly"
                                   ( Generic (_3, _5) )
# 711 "lambdaAst.ml"
               : 'abs_term_grammar))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'type_grammar) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'abs_term_grammar) in
    Obj.repr(
# 97 "lambdaAst.mly"
                                                     ( Abs (_2, _4, _6) )
# 720 "lambdaAst.ml"
               : 'abs_term_grammar))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'abs_term_grammar) in
    Obj.repr(
# 98 "lambdaAst.mly"
                                       ( Generic (_3, _5) )
# 728 "lambdaAst.ml"
               : 'abs_term_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'term_grammar) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'term_grammar) in
    Obj.repr(
# 100 "lambdaAst.mly"
                            ( App (_1, _2) )
# 736 "lambdaAst.ml"
               : 'app_term_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'app_term_grammar) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'term_grammar) in
    Obj.repr(
# 101 "lambdaAst.mly"
                                ( App (_1, _2) )
# 744 "lambdaAst.ml"
               : 'app_term_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'app_term_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'type_grammar) in
    Obj.repr(
# 102 "lambdaAst.mly"
                                              ( TApp (_1, _3) )
# 752 "lambdaAst.ml"
               : 'app_term_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'term_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'type_grammar) in
    Obj.repr(
# 103 "lambdaAst.mly"
                                          ( TApp (_1, _3) )
# 760 "lambdaAst.ml"
               : 'app_term_grammar))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'app_term_grammar) in
    Obj.repr(
# 105 "lambdaAst.mly"
                   ( [_1] )
# 767 "lambdaAst.ml"
               : 'term_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'term_grammar) in
    Obj.repr(
# 106 "lambdaAst.mly"
               ( [_1] )
# 774 "lambdaAst.ml"
               : 'term_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'app_term_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'term_list) in
    Obj.repr(
# 107 "lambdaAst.mly"
                                   ( _1 :: _3 )
# 782 "lambdaAst.ml"
               : 'term_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'term_grammar) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'term_list) in
    Obj.repr(
# 108 "lambdaAst.mly"
                               ( _1 :: _3 )
# 790 "lambdaAst.ml"
               : 'term_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'term_grammar) in
    Obj.repr(
# 110 "lambdaAst.mly"
                   ( _1 )
# 797 "lambdaAst.ml"
               : PreIr.term_ast))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'type_grammar) in
    Obj.repr(
# 112 "lambdaAst.mly"
                   ( _1 )
# 804 "lambdaAst.ml"
               : PreIr.type_ast))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'prop_grammar) in
    Obj.repr(
# 114 "lambdaAst.mly"
                   ( _1 )
# 811 "lambdaAst.ml"
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
