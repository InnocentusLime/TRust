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

open Parsing;;
let _ = parse_error;;
# 6 "lambdaAst.mly"
open PreIr
# 72 "lambdaAst.ml"
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
  313 (* OR_INTROL *);
  314 (* OR_INTROR *);
  315 (* AND_INTRO *);
  316 (* EQ_REFL *);
  317 (* EXIST *);
  318 (* APP *);
  319 (* ABS *);
    0|]

let yytransl_block = [|
  261 (* INT *);
  263 (* VAR *);
    0|]

let yylhs = "\255\255\
\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\
\002\000\002\000\002\000\002\000\003\000\003\000\003\000\003\000\
\003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
\004\000\004\000\004\000\004\000\004\000\004\000\004\000\004\000\
\004\000\004\000\004\000\004\000\004\000\004\000\004\000\004\000\
\004\000\004\000\004\000\004\000\004\000\005\000\005\000\001\000\
\000\000"

let yylen = "\002\000\
\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\
\001\000\001\000\001\000\004\000\005\000\003\000\003\000\003\000\
\007\000\001\000\006\000\006\000\006\000\006\000\006\000\003\000\
\006\000\012\000\014\000\004\000\010\000\006\000\006\000\006\000\
\008\000\010\000\010\000\010\000\014\000\001\000\005\000\003\000\
\005\000\010\000\008\000\008\000\010\000\001\000\002\000\002\000\
\002\000"

let yydefred = "\000\000\
\000\000\000\000\006\000\000\000\000\000\002\000\003\000\001\000\
\005\000\004\000\000\000\000\000\000\000\009\000\008\000\007\000\
\000\000\010\000\011\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\049\000\038\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\048\000\000\000\000\000\000\000\
\000\000\000\000\000\000\047\000\000\000\040\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\024\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\012\000\000\000\000\000\
\000\000\000\000\000\000\000\000\028\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\039\000\000\000\000\000\000\000\000\000\000\000\041\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\013\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\032\000\
\030\000\031\000\000\000\000\000\000\000\025\000\000\000\017\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\033\000\043\000\044\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\035\000\036\000\000\000\034\000\000\000\000\000\029\000\
\045\000\042\000\000\000\000\000\000\000\000\000\026\000\000\000\
\000\000\000\000\037\000\027\000"

let yydgoto = "\002\000\
\038\000\039\000\040\000\041\000\042\000"

let yysindex = "\016\000\
\252\254\000\000\000\000\252\254\252\254\000\000\000\000\000\000\
\000\000\000\000\016\255\017\255\021\255\000\000\000\000\000\000\
\252\254\000\000\000\000\253\254\030\255\031\255\039\255\047\255\
\053\255\055\255\061\255\065\255\078\255\079\255\081\255\088\255\
\089\255\110\255\113\255\117\255\121\255\000\000\000\000\004\000\
\250\254\054\255\015\000\055\000\134\255\136\255\137\255\140\255\
\144\255\255\254\150\255\252\254\252\254\252\254\252\254\252\254\
\252\254\252\254\252\254\252\254\252\254\252\254\252\254\252\254\
\252\254\252\254\252\254\252\254\000\000\252\254\252\254\252\254\
\252\254\054\255\252\254\000\000\252\254\000\000\252\254\252\254\
\252\254\252\254\252\254\252\254\069\255\120\255\056\255\104\255\
\112\255\115\255\118\255\139\255\240\000\143\255\146\255\149\255\
\152\255\159\255\172\255\175\255\179\255\182\255\185\255\035\001\
\241\254\130\255\130\255\000\000\032\001\108\255\167\001\170\001\
\177\001\180\001\187\001\052\255\124\255\000\000\252\254\252\254\
\252\254\252\254\252\254\252\254\000\000\252\254\252\254\252\254\
\252\254\252\254\252\254\252\254\252\254\252\254\252\254\252\254\
\000\000\252\254\252\254\252\254\252\254\252\254\000\000\252\254\
\188\255\195\255\208\255\211\255\215\255\218\255\221\255\224\255\
\061\001\076\001\079\001\231\255\254\255\084\000\098\001\113\000\
\000\000\059\255\059\255\130\255\130\255\130\255\228\255\252\254\
\252\254\252\254\252\254\252\254\252\254\252\254\252\254\000\000\
\000\000\000\000\252\254\252\254\252\254\000\000\252\254\000\000\
\178\000\181\000\184\000\188\000\227\000\232\000\236\000\110\001\
\118\001\122\001\243\000\247\000\252\254\252\254\252\254\252\254\
\252\254\252\254\252\254\000\000\000\000\000\000\252\254\252\254\
\125\001\130\001\252\000\137\001\000\001\039\001\142\001\145\001\
\149\001\000\000\000\000\252\254\000\000\252\254\252\254\000\000\
\000\000\000\000\045\001\157\001\048\001\252\254\000\000\252\254\
\161\001\164\001\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\001\000\059\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\146\000\062\000\088\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\149\000\159\000\091\000\117\000\120\000\000\000\000\000\
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
\000\000\000\000\162\001\216\255\000\000"

let yytablesize = 726
let yytable = "\073\000\
\046\000\076\000\003\000\069\000\004\000\070\000\005\000\072\000\
\006\000\007\000\008\000\009\000\010\000\011\000\012\000\013\000\
\001\000\045\000\047\000\070\000\071\000\072\000\046\000\048\000\
\014\000\015\000\016\000\049\000\017\000\051\000\084\000\074\000\
\085\000\108\000\018\000\019\000\020\000\021\000\022\000\023\000\
\052\000\053\000\024\000\025\000\026\000\027\000\028\000\029\000\
\030\000\054\000\031\000\032\000\033\000\034\000\035\000\036\000\
\037\000\055\000\018\000\119\000\003\000\016\000\004\000\056\000\
\005\000\057\000\006\000\007\000\008\000\009\000\010\000\058\000\
\070\000\071\000\072\000\059\000\070\000\071\000\072\000\070\000\
\071\000\072\000\014\000\015\000\016\000\143\000\075\000\014\000\
\060\000\061\000\022\000\062\000\018\000\019\000\020\000\021\000\
\022\000\023\000\063\000\064\000\024\000\025\000\026\000\027\000\
\028\000\029\000\030\000\120\000\031\000\032\000\033\000\034\000\
\035\000\036\000\037\000\121\000\021\000\137\000\122\000\023\000\
\065\000\123\000\117\000\066\000\070\000\071\000\072\000\067\000\
\070\000\071\000\072\000\068\000\070\000\071\000\072\000\070\000\
\071\000\072\000\070\000\071\000\072\000\079\000\124\000\080\000\
\081\000\015\000\126\000\082\000\020\000\127\000\070\000\083\000\
\128\000\118\000\086\000\129\000\144\000\000\000\019\000\070\000\
\071\000\072\000\130\000\070\000\071\000\072\000\070\000\071\000\
\072\000\070\000\071\000\072\000\070\000\071\000\072\000\131\000\
\000\000\000\000\132\000\070\000\071\000\072\000\133\000\000\000\
\000\000\134\000\000\000\000\000\135\000\000\000\000\000\168\000\
\070\000\071\000\072\000\070\000\071\000\072\000\169\000\070\000\
\071\000\072\000\070\000\071\000\072\000\070\000\071\000\072\000\
\070\000\071\000\072\000\170\000\000\000\000\000\171\000\070\000\
\071\000\072\000\172\000\000\000\000\000\173\000\000\000\000\000\
\174\000\000\000\000\000\175\000\070\000\071\000\072\000\070\000\
\071\000\072\000\179\000\070\000\071\000\072\000\070\000\071\000\
\072\000\070\000\071\000\072\000\070\000\071\000\072\000\000\000\
\070\000\071\000\072\000\070\000\071\000\072\000\000\000\000\000\
\000\000\180\000\000\000\000\000\046\000\184\000\000\000\046\000\
\000\000\046\000\046\000\046\000\046\000\046\000\046\000\046\000\
\046\000\046\000\070\000\071\000\072\000\046\000\046\000\046\000\
\070\000\071\000\072\000\046\000\046\000\046\000\046\000\046\000\
\046\000\046\000\046\000\070\000\071\000\072\000\000\000\046\000\
\046\000\046\000\046\000\046\000\046\000\000\000\077\000\046\000\
\046\000\046\000\046\000\046\000\046\000\046\000\000\000\046\000\
\046\000\046\000\046\000\046\000\046\000\046\000\018\000\000\000\
\000\000\016\000\078\000\000\000\018\000\000\000\018\000\016\000\
\000\000\016\000\000\000\070\000\071\000\072\000\000\000\018\000\
\018\000\018\000\000\000\016\000\016\000\018\000\018\000\181\000\
\016\000\016\000\018\000\014\000\018\000\016\000\022\000\016\000\
\000\000\014\000\000\000\014\000\022\000\000\000\022\000\000\000\
\070\000\071\000\072\000\000\000\000\000\014\000\014\000\000\000\
\022\000\022\000\014\000\014\000\183\000\022\000\022\000\014\000\
\021\000\014\000\022\000\023\000\022\000\000\000\021\000\000\000\
\021\000\023\000\000\000\023\000\000\000\070\000\071\000\072\000\
\000\000\000\000\021\000\021\000\000\000\023\000\023\000\021\000\
\021\000\000\000\023\000\023\000\021\000\015\000\021\000\023\000\
\020\000\023\000\000\000\015\000\000\000\015\000\020\000\000\000\
\020\000\000\000\019\000\000\000\000\000\043\000\044\000\015\000\
\019\000\000\000\019\000\000\000\015\000\015\000\000\000\020\000\
\020\000\015\000\050\000\015\000\020\000\197\000\020\000\000\000\
\198\000\019\000\019\000\199\000\000\000\000\000\019\000\200\000\
\019\000\000\000\000\000\000\000\000\000\000\000\070\000\071\000\
\072\000\070\000\071\000\072\000\070\000\071\000\072\000\000\000\
\070\000\071\000\072\000\000\000\000\000\087\000\088\000\089\000\
\090\000\091\000\092\000\093\000\094\000\095\000\096\000\097\000\
\098\000\099\000\100\000\101\000\102\000\103\000\201\000\104\000\
\105\000\106\000\107\000\202\000\109\000\000\000\110\000\203\000\
\111\000\112\000\113\000\114\000\115\000\116\000\207\000\070\000\
\071\000\072\000\208\000\125\000\070\000\071\000\072\000\220\000\
\070\000\071\000\072\000\222\000\070\000\071\000\072\000\070\000\
\071\000\072\000\000\000\070\000\071\000\072\000\000\000\000\000\
\070\000\071\000\072\000\000\000\070\000\071\000\072\000\000\000\
\145\000\146\000\147\000\148\000\149\000\150\000\000\000\151\000\
\152\000\153\000\154\000\155\000\156\000\157\000\158\000\159\000\
\160\000\161\000\223\000\162\000\163\000\164\000\165\000\166\000\
\230\000\167\000\000\000\232\000\070\000\071\000\072\000\070\000\
\071\000\072\000\000\000\070\000\071\000\072\000\136\000\084\000\
\000\000\070\000\071\000\072\000\070\000\071\000\072\000\000\000\
\176\000\185\000\186\000\187\000\188\000\189\000\190\000\191\000\
\192\000\070\000\071\000\072\000\193\000\194\000\195\000\177\000\
\196\000\000\000\178\000\000\000\000\000\000\000\000\000\000\000\
\070\000\071\000\072\000\070\000\071\000\072\000\209\000\210\000\
\211\000\212\000\213\000\214\000\215\000\182\000\000\000\000\000\
\216\000\217\000\000\000\000\000\000\000\000\000\070\000\071\000\
\072\000\204\000\000\000\000\000\000\000\227\000\000\000\228\000\
\229\000\205\000\070\000\071\000\072\000\206\000\000\000\233\000\
\218\000\234\000\070\000\071\000\072\000\219\000\070\000\071\000\
\072\000\070\000\071\000\072\000\221\000\000\000\070\000\071\000\
\072\000\224\000\000\000\000\000\225\000\070\000\071\000\072\000\
\226\000\000\000\070\000\071\000\072\000\070\000\071\000\072\000\
\231\000\070\000\071\000\072\000\235\000\000\000\000\000\236\000\
\000\000\070\000\071\000\072\000\000\000\070\000\071\000\072\000\
\070\000\071\000\072\000\070\000\071\000\072\000\070\000\071\000\
\072\000\138\000\000\000\000\000\139\000\070\000\071\000\072\000\
\070\000\071\000\072\000\140\000\000\000\000\000\141\000\070\000\
\071\000\072\000\000\000\000\000\000\000\142\000"

let yycheck = "\006\001\
\000\000\042\000\007\001\000\000\009\001\021\001\011\001\023\001\
\013\001\014\001\015\001\016\001\017\001\018\001\019\001\020\001\
\001\000\002\001\002\001\021\001\022\001\023\001\007\001\007\001\
\029\001\030\001\031\001\007\001\033\001\033\001\032\001\038\001\
\034\001\074\000\039\001\040\001\041\001\042\001\043\001\044\001\
\011\001\011\001\047\001\048\001\049\001\050\001\051\001\052\001\
\053\001\011\001\055\001\056\001\057\001\058\001\059\001\060\001\
\061\001\011\001\000\000\004\001\007\001\000\000\009\001\011\001\
\011\001\011\001\013\001\014\001\015\001\016\001\017\001\011\001\
\021\001\022\001\023\001\011\001\021\001\022\001\023\001\021\001\
\022\001\023\001\029\001\030\001\031\001\034\001\033\001\000\000\
\011\001\011\001\000\000\011\001\039\001\040\001\041\001\042\001\
\043\001\044\001\011\001\011\001\047\001\048\001\049\001\050\001\
\051\001\052\001\053\001\004\001\055\001\056\001\057\001\058\001\
\059\001\060\001\061\001\004\001\000\000\010\001\004\001\000\000\
\011\001\004\001\054\001\011\001\021\001\022\001\023\001\011\001\
\021\001\022\001\023\001\011\001\021\001\022\001\023\001\021\001\
\022\001\023\001\021\001\022\001\023\001\008\001\004\001\008\001\
\008\001\000\000\004\001\008\001\000\000\004\001\021\001\008\001\
\004\001\034\001\005\001\004\001\033\001\255\255\000\000\021\001\
\022\001\023\001\004\001\021\001\022\001\023\001\021\001\022\001\
\023\001\021\001\022\001\023\001\021\001\022\001\023\001\004\001\
\255\255\255\255\004\001\021\001\022\001\023\001\004\001\255\255\
\255\255\004\001\255\255\255\255\004\001\255\255\255\255\004\001\
\021\001\022\001\023\001\021\001\022\001\023\001\004\001\021\001\
\022\001\023\001\021\001\022\001\023\001\021\001\022\001\023\001\
\021\001\022\001\023\001\004\001\255\255\255\255\004\001\021\001\
\022\001\023\001\004\001\255\255\255\255\004\001\255\255\255\255\
\004\001\255\255\255\255\004\001\021\001\022\001\023\001\021\001\
\022\001\023\001\004\001\021\001\022\001\023\001\021\001\022\001\
\023\001\021\001\022\001\023\001\021\001\022\001\023\001\255\255\
\021\001\022\001\023\001\021\001\022\001\023\001\255\255\255\255\
\255\255\004\001\255\255\255\255\004\001\034\001\255\255\007\001\
\255\255\009\001\010\001\011\001\012\001\013\001\014\001\015\001\
\016\001\017\001\021\001\022\001\023\001\021\001\022\001\023\001\
\021\001\022\001\023\001\027\001\028\001\029\001\030\001\031\001\
\032\001\033\001\034\001\021\001\022\001\023\001\255\255\039\001\
\040\001\041\001\042\001\043\001\044\001\255\255\032\001\047\001\
\048\001\049\001\050\001\051\001\052\001\053\001\255\255\055\001\
\056\001\057\001\058\001\059\001\060\001\061\001\004\001\255\255\
\255\255\004\001\012\001\255\255\010\001\255\255\012\001\010\001\
\255\255\012\001\255\255\021\001\022\001\023\001\255\255\021\001\
\022\001\023\001\255\255\022\001\023\001\027\001\028\001\004\001\
\027\001\028\001\032\001\004\001\034\001\032\001\004\001\034\001\
\255\255\010\001\255\255\012\001\010\001\255\255\012\001\255\255\
\021\001\022\001\023\001\255\255\255\255\022\001\023\001\255\255\
\022\001\023\001\027\001\028\001\004\001\027\001\028\001\032\001\
\004\001\034\001\032\001\004\001\034\001\255\255\010\001\255\255\
\012\001\010\001\255\255\012\001\255\255\021\001\022\001\023\001\
\255\255\255\255\022\001\023\001\255\255\022\001\023\001\027\001\
\028\001\255\255\027\001\028\001\032\001\004\001\034\001\032\001\
\004\001\034\001\255\255\010\001\255\255\012\001\010\001\255\255\
\012\001\255\255\004\001\255\255\255\255\004\000\005\000\022\001\
\010\001\255\255\012\001\255\255\027\001\028\001\255\255\027\001\
\028\001\032\001\017\000\034\001\032\001\004\001\034\001\255\255\
\004\001\027\001\028\001\004\001\255\255\255\255\032\001\004\001\
\034\001\255\255\255\255\255\255\255\255\255\255\021\001\022\001\
\023\001\021\001\022\001\023\001\021\001\022\001\023\001\255\255\
\021\001\022\001\023\001\255\255\255\255\052\000\053\000\054\000\
\055\000\056\000\057\000\058\000\059\000\060\000\061\000\062\000\
\063\000\064\000\065\000\066\000\067\000\068\000\004\001\070\000\
\071\000\072\000\073\000\004\001\075\000\255\255\077\000\004\001\
\079\000\080\000\081\000\082\000\083\000\084\000\004\001\021\001\
\022\001\023\001\004\001\012\001\021\001\022\001\023\001\004\001\
\021\001\022\001\023\001\004\001\021\001\022\001\023\001\021\001\
\022\001\023\001\255\255\021\001\022\001\023\001\255\255\255\255\
\021\001\022\001\023\001\255\255\021\001\022\001\023\001\255\255\
\119\000\120\000\121\000\122\000\123\000\124\000\255\255\126\000\
\127\000\128\000\129\000\130\000\131\000\132\000\133\000\134\000\
\135\000\136\000\004\001\138\000\139\000\140\000\141\000\142\000\
\004\001\144\000\255\255\004\001\021\001\022\001\023\001\021\001\
\022\001\023\001\255\255\021\001\022\001\023\001\028\001\032\001\
\255\255\021\001\022\001\023\001\021\001\022\001\023\001\255\255\
\012\001\168\000\169\000\170\000\171\000\172\000\173\000\174\000\
\175\000\021\001\022\001\023\001\179\000\180\000\181\000\012\001\
\183\000\255\255\012\001\255\255\255\255\255\255\255\255\255\255\
\021\001\022\001\023\001\021\001\022\001\023\001\197\000\198\000\
\199\000\200\000\201\000\202\000\203\000\012\001\255\255\255\255\
\207\000\208\000\255\255\255\255\255\255\255\255\021\001\022\001\
\023\001\012\001\255\255\255\255\255\255\220\000\255\255\222\000\
\223\000\012\001\021\001\022\001\023\001\012\001\255\255\230\000\
\012\001\232\000\021\001\022\001\023\001\012\001\021\001\022\001\
\023\001\021\001\022\001\023\001\012\001\255\255\021\001\022\001\
\023\001\012\001\255\255\255\255\012\001\021\001\022\001\023\001\
\012\001\255\255\021\001\022\001\023\001\021\001\022\001\023\001\
\012\001\021\001\022\001\023\001\012\001\255\255\255\255\012\001\
\255\255\021\001\022\001\023\001\255\255\021\001\022\001\023\001\
\021\001\022\001\023\001\021\001\022\001\023\001\021\001\022\001\
\023\001\027\001\255\255\255\255\027\001\021\001\022\001\023\001\
\021\001\022\001\023\001\027\001\255\255\255\255\027\001\021\001\
\022\001\023\001\255\255\255\255\255\255\027\001"

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
  OR_INTROL\000\
  OR_INTROR\000\
  AND_INTRO\000\
  EQ_REFL\000\
  EXIST\000\
  APP\000\
  ABS\000\
  "

let yynames_block = "\
  INT\000\
  VAR\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    Obj.repr(
# 68 "lambdaAst.mly"
      ( Nil )
# 526 "lambdaAst.ml"
               : 'const))
; (fun __caml_parser_env ->
    Obj.repr(
# 69 "lambdaAst.mly"
       ( NatO )
# 532 "lambdaAst.ml"
               : 'const))
; (fun __caml_parser_env ->
    Obj.repr(
# 70 "lambdaAst.mly"
       ( NatSucc )
# 538 "lambdaAst.ml"
               : 'const))
; (fun __caml_parser_env ->
    Obj.repr(
# 71 "lambdaAst.mly"
        ( BoolFalse )
# 544 "lambdaAst.ml"
               : 'const))
; (fun __caml_parser_env ->
    Obj.repr(
# 72 "lambdaAst.mly"
       ( BoolTrue )
# 550 "lambdaAst.ml"
               : 'const))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 73 "lambdaAst.mly"
      ( Var _1 )
# 557 "lambdaAst.ml"
               : 'const))
; (fun __caml_parser_env ->
    Obj.repr(
# 74 "lambdaAst.mly"
      ( Nat )
# 563 "lambdaAst.ml"
               : 'const))
; (fun __caml_parser_env ->
    Obj.repr(
# 75 "lambdaAst.mly"
       ( Bool )
# 569 "lambdaAst.ml"
               : 'const))
; (fun __caml_parser_env ->
    Obj.repr(
# 76 "lambdaAst.mly"
       ( Unit )
# 575 "lambdaAst.ml"
               : 'const))
; (fun __caml_parser_env ->
    Obj.repr(
# 77 "lambdaAst.mly"
       ( Prop )
# 581 "lambdaAst.ml"
               : 'const))
; (fun __caml_parser_env ->
    Obj.repr(
# 78 "lambdaAst.mly"
        ( Small )
# 587 "lambdaAst.ml"
               : 'const))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : int) in
    Obj.repr(
# 79 "lambdaAst.mly"
                   ( Type _3 )
# 594 "lambdaAst.ml"
               : 'const))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : 'term) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 81 "lambdaAst.mly"
                              ( Eq (_1, _3, _5) )
# 603 "lambdaAst.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'atom_term) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 82 "lambdaAst.mly"
                       ( Forall ("_", _1, _3) )
# 611 "lambdaAst.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 83 "lambdaAst.mly"
                     ( Conjunction (_1, _3) )
# 619 "lambdaAst.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 84 "lambdaAst.mly"
                    ( Disjunction (_1, _3) )
# 627 "lambdaAst.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : 'term) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 85 "lambdaAst.mly"
                                      ( Sumbool (_2, _6) )
# 635 "lambdaAst.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'app_term) in
    Obj.repr(
# 86 "lambdaAst.mly"
                     ( _1 )
# 642 "lambdaAst.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 87 "lambdaAst.mly"
                                           ( Abs (_2, _4, _6) )
# 651 "lambdaAst.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 88 "lambdaAst.mly"
                                                ( Abs ("_", _4, _6) )
# 659 "lambdaAst.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 89 "lambdaAst.mly"
                                  ( Forall (_2, _4, _6) )
# 668 "lambdaAst.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 90 "lambdaAst.mly"
                                       ( Forall ("_", _4, _6) )
# 676 "lambdaAst.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 91 "lambdaAst.mly"
                                  ( Exists (_2, _4, _6) )
# 685 "lambdaAst.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'atom_term) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'atom_term) in
    Obj.repr(
# 92 "lambdaAst.mly"
                              ( Subtyping (_1, _3) )
# 693 "lambdaAst.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'term) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 94 "lambdaAst.mly"
                                             ( EqRefl (_3, _5) )
# 701 "lambdaAst.ml"
               : 'atom_term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 9 : 'term) in
    let _5 = (Parsing.peek_val __caml_parser_env 7 : 'term) in
    let _7 = (Parsing.peek_val __caml_parser_env 5 : 'term) in
    let _9 = (Parsing.peek_val __caml_parser_env 3 : 'term) in
    let _11 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 95 "lambdaAst.mly"
                                                                                              ( SubTrans (_3, _5, _7, _9, _11) )
# 712 "lambdaAst.ml"
               : 'atom_term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 11 : 'term) in
    let _5 = (Parsing.peek_val __caml_parser_env 9 : 'term) in
    let _7 = (Parsing.peek_val __caml_parser_env 7 : 'term) in
    let _9 = (Parsing.peek_val __caml_parser_env 5 : 'term) in
    let _11 = (Parsing.peek_val __caml_parser_env 3 : 'term) in
    let _13 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 96 "lambdaAst.mly"
                                                                                                             ( SubProd (_3, _5, _7, _9, _11, _13) )
# 724 "lambdaAst.ml"
               : 'atom_term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 97 "lambdaAst.mly"
                             ( SubRefl _3 )
# 731 "lambdaAst.ml"
               : 'atom_term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 7 : 'term) in
    let _5 = (Parsing.peek_val __caml_parser_env 5 : 'term) in
    let _7 = (Parsing.peek_val __caml_parser_env 3 : 'term) in
    let _9 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 98 "lambdaAst.mly"
                                                                            ( SubSub (_3, _5, _7, _9) )
# 741 "lambdaAst.ml"
               : 'atom_term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'term) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 99 "lambdaAst.mly"
                                            ( SBLeft (_3, _5) )
# 749 "lambdaAst.ml"
               : 'atom_term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'term) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 100 "lambdaAst.mly"
                                            ( SBRight (_3, _5) )
# 757 "lambdaAst.ml"
               : 'atom_term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'term) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 101 "lambdaAst.mly"
                                                 ( SubUnrefine (_3, _5) )
# 765 "lambdaAst.ml"
               : 'atom_term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : 'term) in
    let _5 = (Parsing.peek_val __caml_parser_env 3 : 'term) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 102 "lambdaAst.mly"
                                                            ( SubGen (_3, _5, _7) )
# 774 "lambdaAst.ml"
               : 'atom_term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 7 : 'term) in
    let _5 = (Parsing.peek_val __caml_parser_env 5 : 'term) in
    let _7 = (Parsing.peek_val __caml_parser_env 3 : 'term) in
    let _9 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 103 "lambdaAst.mly"
                                                                                ( Membership (_3, _5, _7, _9) )
# 784 "lambdaAst.ml"
               : 'atom_term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 7 : 'term) in
    let _5 = (Parsing.peek_val __caml_parser_env 5 : 'term) in
    let _7 = (Parsing.peek_val __caml_parser_env 3 : 'term) in
    let _9 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 104 "lambdaAst.mly"
                                                                            ( NatRec (_3, _5, _7, _9) )
# 794 "lambdaAst.ml"
               : 'atom_term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 7 : 'term) in
    let _5 = (Parsing.peek_val __caml_parser_env 5 : 'term) in
    let _7 = (Parsing.peek_val __caml_parser_env 3 : 'term) in
    let _9 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 105 "lambdaAst.mly"
                                                                             ( BoolRec (_3, _5, _7, _9) )
# 804 "lambdaAst.ml"
               : 'atom_term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 11 : 'term) in
    let _5 = (Parsing.peek_val __caml_parser_env 9 : 'term) in
    let _7 = (Parsing.peek_val __caml_parser_env 7 : 'term) in
    let _9 = (Parsing.peek_val __caml_parser_env 5 : 'term) in
    let _11 = (Parsing.peek_val __caml_parser_env 3 : 'term) in
    let _13 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 106 "lambdaAst.mly"
                                                                                                                ( SumboolRec (_3, _5, _7, _9, _11, _13) )
# 816 "lambdaAst.ml"
               : 'atom_term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'const) in
    Obj.repr(
# 107 "lambdaAst.mly"
        ( _1 )
# 823 "lambdaAst.ml"
               : 'atom_term))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'term) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 108 "lambdaAst.mly"
                              ( Refine (_2, _4) )
# 831 "lambdaAst.ml"
               : 'atom_term))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 109 "lambdaAst.mly"
                     ( _2 )
# 838 "lambdaAst.ml"
               : 'atom_term))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'term) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 110 "lambdaAst.mly"
                        ( Sumbool (_2, _4) )
# 846 "lambdaAst.ml"
               : 'atom_term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 7 : 'term) in
    let _5 = (Parsing.peek_val __caml_parser_env 5 : 'term) in
    let _7 = (Parsing.peek_val __caml_parser_env 3 : 'term) in
    let _9 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 111 "lambdaAst.mly"
                                                                           ( Exist (_3, _5, _7, _9) )
# 856 "lambdaAst.ml"
               : 'atom_term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : 'term) in
    let _5 = (Parsing.peek_val __caml_parser_env 3 : 'term) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 112 "lambdaAst.mly"
                                                               ( OrIntroL (_3, _5, _7) )
# 865 "lambdaAst.ml"
               : 'atom_term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : 'term) in
    let _5 = (Parsing.peek_val __caml_parser_env 3 : 'term) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 113 "lambdaAst.mly"
                                                               ( OrIntroR (_3, _5, _7) )
# 874 "lambdaAst.ml"
               : 'atom_term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 7 : 'term) in
    let _5 = (Parsing.peek_val __caml_parser_env 5 : 'term) in
    let _7 = (Parsing.peek_val __caml_parser_env 3 : 'term) in
    let _9 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 114 "lambdaAst.mly"
                                                                               ( AndIntro (_3, _5, _7, _9) )
# 884 "lambdaAst.ml"
               : 'atom_term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'atom_term) in
    Obj.repr(
# 116 "lambdaAst.mly"
            ( _1 )
# 891 "lambdaAst.ml"
               : 'app_term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'app_term) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'atom_term) in
    Obj.repr(
# 117 "lambdaAst.mly"
                     ( App (_1, _2) )
# 899 "lambdaAst.ml"
               : 'app_term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 119 "lambdaAst.mly"
           ( _1 )
# 906 "lambdaAst.ml"
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
