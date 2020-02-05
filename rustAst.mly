%{
open RustAstTypes;;
%}

%token <string> INT
%token <string> IDENT
%token <string> COMMENT
%token PLUS MINUS MULTIPLY DIVIDE
%token UMINUS
%token LANGLE RANGLE LANGLE_EQ RANGLE_EQ EQ
%token NEWLINE
%token EOF
%token LPAREN RPAREN
%token LBRACE RBRACE
%token IF ELSE FN
%token ARROW
%token COMMA
%token CALL
%token UNIT UNIT_T
%token INT_T
%token COLLON
%token VAL PROVE_TERMINATION WITH
%token PROPAND PROPOR POROPIMPLIES PROPEQ
%token PURE DIV
%token FATARROW

%left FATARROW
%left PROPOR
%left PROPAND
%nonassoc PROPEQ             
%nonassoc EQ
%nonassoc LANGLE RANGLE LANGLE_EQ RANGLE_EQ
%left PLUS MINUS
%left MULTIPLY DIVIDE
%nonassoc UMINUS
%left LPAREN LBRACE
%nonassoc CALL
%left COMMENT

%start rust_file trust_command
%type <item list> rust_file
%type <TrustAstTypes.trust_command> trust_command
%%
trust_command:
	| VAL IDENT COLLON trust_domain_typ { TrustAstTypes.Val ($2, $4) }
	| PROVE_TERMINATION IDENT WITH IDENT { TrustAstTypes.TerminationProof ($2, $4) }
;
trust_refinement_typ:
	| trust_well_formed_typ { Simple $1 }
	| IDENT COLLON trust_well_formed_typ { Named ($1, $3) }
	| IDENT COLLON trust_well_formed_typ LBRACE prop RBRACE { NamedRefined ($1, $3, $5) }
	| trust_well_formed_typ LBRACE prop RBRACE { Refined ($1, $3) }
;
trust_well_formed_typ:
	| UNIT_T { TrustAstTypes.Unit }
	| INT_T { TrustAstTypes.Int }
	| LPAREN trust_ill_formed_typ RPAREN { $2 }
;
trust_domain_typ:
	| trust_ill_formed_typ { TrustAstTypes.Simple $1 }
	| trust_refinement_typ { $1 }
;
trust_ill_formed_typ:
	| trust_refinement_typ ARROW trust_domain_typ { TrustAstTypes.Arrow ($1, $3) }
	| trust_refinement_typ ARROW PURE trust_domain_typ { TrustAstTypes.EffectArrow ($1, TrustAstTypes.Pure, $4) }
	| trust_refinement_typ ARROW DIV trust_domain_typ { TrustAstTypes.Arrow ($1, TrustAstTypes.Div, $4) }
;
prop:
	| LPAREN prop RPAREN { $2 }
	| prop FATARROW prop { TrustAstTypes.Implies ($1, $3) }
	| prop PROPAND prop { TrustAstTypes.And ($1, $3) }
	| prop PROPOR prop { TrustAstTypes.Or ($1, $3) }
	| exp PROPEQ exp { TrustAstTypes.PropEq ($1, $3) }
;

rust_file:
	| COMMENT rust_file { (Comment $1) :: $2 }
	| fn_def rust_file { (FnDef $1) :: $2 }
	| EOF { [] }
; 
fn_def:
	| FN IDENT LPAREN fn_args RPAREN ARROW typ LBRACE exp RBRACE { ($2, $4, $7, $9) }
;
fn_args:
	| fn_args_sub { $1 }
	| { [] }
fn_args_sub:
	| fn_arg COMMA fn_args_sub { $1 :: $3 }
	| fn_arg { $1 :: [] }
fn_arg:
	| IDENT COLLON typ { ($1, $3) }
typ:
	| UNIT { Unit }
	| INT_T { Int }
	| FN LPAREN maybe_typs RPAREN ARROW typ { Fn ($3, $6) }
;
maybe_typs:
	| typs { $1 }
	| { [] }
;
typs:
	| typ COMMA typs { $1 :: $3 }
	| typ { $1 :: [] }
;                                                
exp:
	| UNIT { Nil } 
	| exp LPAREN maybe_exps RPAREN %prec CALL { Call ($1, $3) }
	| IDENT { Variable $1 }
	| INT { Const $1 }
	| LPAREN exp RPAREN { $2 }
	| exp PLUS exp { Add ($1, $3) }
	| exp MINUS exp { Sub ($1, $3) }
	| exp MULTIPLY exp { Multiply ($1, $3) }
	| exp DIVIDE exp { Divide ($1, $3) }
	| exp LANGLE exp { Less ($1, $3) }
	| exp RANGLE exp { Greater ($1, $3) }
	| exp LANGLE_EQ exp { LessEqual ($1, $3) }
	| exp RANGLE_EQ exp { GreaterEqual ($1, $3) }
	| exp EQ exp { Equal ($1, $3) }
	| MINUS exp %prec UMINUS { Negotiate $2 }
	| ifthenelse { $1 }
;
maybe_exps:
	| { [] }
	| exps { $1 }
exps:
	| exp COMMA exps { $1 :: $3 }
	| exp { $1 :: [] }
;
ifthenelse:
	| IF exp LBRACE exp RBRACE ELSE ifthenelse { IfThenElse ($2, $4, $7) }
	| IF exp LBRACE exp RBRACE ELSE LBRACE exp RBRACE { IfThenElse ($2, $4, $8) }
	| IF exp LBRACE exp RBRACE { IfThen ($2, $4) }
;
