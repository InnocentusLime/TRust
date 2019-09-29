%{
open PreIr;;
%}

%token EOF
%token COMMA
%token <int> INT
%token ARROW
%token <string> VAR
%token COLLON
%token LBRACE RBRACE
%token LPARAN RPARAN
%token ZERO
%token SUCC
%token NIL
%token TRUE FALSE
%token FOR IF THEN ELSE DO
%token SLASH FORALL EXISTS
%token EQ
%token PROP_AND PROP_OR PROP_IMPLIES
%token TOP BOT
%token DOT
%token TYPE_HINT
%token UNIT BOOL NAT
%token FAT_ARROW
%token GENERIC_TYPE ARROW_TYPE REFINED_TYPE
%token BAR
%token LSQ RSQ
%token APP
%token PROD
%token LANGLE RANGLE

%left FAT_ARROW PROP_IMPLIES
%left PROP_OR
%left PROP_AND
%left GENERIC_TYPE
%left ARROW_TYPE ARROW
%left DEP_TYPE
%left PROD
%nonassoc EQ
%left COMMA
%left LPARAN LBRACE LSQ
%left APP

%start lambda_term lambda_type lambda_prop
%type <PreIr.term_ast> lambda_term
%type <PreIr.type_ast> lambda_type
%type <PreIr.prop_ast> lambda_prop
%%

prop_grammar:
| TOP { Top }
| BOT { Bot }
| LPARAN prop_grammar RPARAN { $2 }
| prop_grammar PROP_AND prop_grammar { Conjunction ($1, $3) }
| prop_grammar PROP_OR prop_grammar { Disjunction ($1, $3) }
| prop_grammar FAT_ARROW prop_grammar %prec PROP_IMPLIES { Implication ($1, $3) }
| term_grammar EQ term_grammar TYPE_HINT type_grammar { Eq ($1, $3, $5) }
| FORALL VAR COLLON type_grammar DOT prop_grammar %prec PROP_IMPLIES { Forall ($2, $4, $6) }
| EXISTS VAR COLLON type_grammar DOT prop_grammar %prec PROP_IMPLIES { Exists ($2, $4, $6) }
| FORALL VAR DOT prop_grammar %prec PROP_IMPLIES { ForallGen ($2, $4) }
atom_type_grammar:
| BOOL { Bool }
| UNIT { Unit }
| NAT { Nat }
| VAR { TVar $1 }
| LPARAN type_grammar RPARAN { $2 }
type_grammar:
| atom_type_grammar { $1 }
| type_grammar ARROW type_grammar %prec ARROW_TYPE { Map ("_", $1, $3) }
| LPARAN VAR COLLON type_grammar RPARAN ARROW type_grammar %prec DEP_TYPE { Map ($2, $4, $7) }
| FORALL VAR DOT type_grammar %prec GENERIC_TYPE { Gen ($2, $4) }
| LBRACE VAR COLLON type_grammar BAR prop_grammar RBRACE %prec REFINED_TYPE { Refine ($2, $4, $6) }
| prod_type %prec PROD { Prod $1 }
prod_type:
| atom_type_grammar PROD atom_type_grammar { [$1; $3] }
| atom_type_grammar PROD prod_type { $1 :: $3 }
term_grammar:
| NIL { Nil }
| ZERO { NatO }
| SUCC { NatSucc }
| FALSE { False }
| TRUE { True }
| VAR { Var $1 }
| LPARAN app_term_grammar RPARAN { $2 }
| LPARAN SLASH VAR COLLON type_grammar DOT app_term_grammar RPARAN { Abs ($3, $5, $7) }
| LPARAN SLASH VAR COLLON type_grammar DOT term_grammar RPARAN { Abs ($3, $5, $7) }
| LPARAN SLASH SLASH VAR DOT app_term_grammar RPARAN { Generic ($4, $6) }
| LPARAN SLASH SLASH VAR DOT term_grammar RPARAN { Generic ($4, $6) }
| term_grammar DOT INT { Proj ($1, $3) }
| LSQ term_list RSQ { Tuple $2 }
| IF term_grammar LANGLE prop_grammar RANGLE THEN LBRACE term_grammar RBRACE ELSE LBRACE term_grammar RBRACE { Ite ($2, $8, $12, $4) }
| FOR term_grammar LANGLE prop_grammar RANGLE DO LBRACE term_grammar RBRACE LBRACE term_grammar RBRACE { For ($2, $8, $11, $4) }
| IF term_grammar THEN LBRACE term_grammar RBRACE ELSE LBRACE term_grammar RBRACE { Ite ($2, $5, $9, Top) }
| FOR term_grammar DO LBRACE term_grammar RBRACE LBRACE term_grammar RBRACE { For ($2, $5, $8, Top) }
app_term_grammar:
| term_grammar term_grammar %prec APP { App ($1, $2) }
| app_term_grammar term_grammar %prec APP { App ($1, $2) }
| app_term_grammar LPARAN type_grammar RPARAN %prec APP { TApp ($1, $3) }
| term_grammar LPARAN type_grammar RPARAN %prec APP { TApp ($1, $3) }
term_list:
| app_term_grammar { [$1] }
| term_grammar { [$1] }
| app_term_grammar COMMA term_list { $1 :: $3 }
| term_grammar COMMA term_list { $1 :: $3 }
lambda_term:
| term_grammar EOF { $1 }
lambda_type:
| type_grammar EOF { $1 }
lambda_prop:
| prop_grammar EOF { $1 }