%{
(*INSRTIONEND*)
%}

%token TRUTH FALSITY
%token <string> INT
%token <string> IDENT
%token <string> SPECIAL_IDENT
%token <string> COMMENT
%token <string> FN_PTR
%token LET EQ
%token PLUS MINUS MULTIPLY DIVIDE
%token UMINUS
%token LANGLE RANGLE LANGLE_EQ RANGLE_EQ LONG_EQ
%token NEWLINE
%token EOF
%token SEMICOLLON
%token LPARAN RPARAN
%token LBRACE RBRACE
%token LSQBR RSQBR
%token IF ELSE FN
%token ARROW
%token COMMA
%token CALL
%token INT_T
%token COLLON
%token TYPE_HINT AT
%token PROPAND PROPOR PROP_IMPLICATION PROPEQ
%token FATARROW
%token TOTAL DIVERGENT MAX_COMP_KIND
%token <string> STRING
%token FORALL SLASH DOT
%token PROPOSITION TYPE PRE_TYPE KIND COMPUTATION_KIND PREDICATE
%token QUIT RESET AXIOM TC_IR_TERM IR_DEFINITION IR_PRINT_DEFINITION
%token REC
%token AND_INTRO OR_INTRO_L OR_INTRO_R AND_ELIM_L AND_ELIM_R OR_ELIM EQ_INTRO EQ_ELIM FALSE_ELIM_PROP FALSE_ELIM_TYPE
%token FN_PTR_TYPE DEREF_FN_PTR
%token TRUTH PROOF_OF_TRUTH FALSITY

%nonassoc EQ
%right PROP_IMPLICATION FORALL
%left PROPOR
%left PROPAND
%nonassoc PROPEQ             
%nonassoc LONG_EQ
%nonassoc LANGLE RANGLE LANGLE_EQ RANGLE_EQ
%left PLUS MINUS
%left MULTIPLY DIVIDE
%nonassoc UMINUS
%nonassoc CALL
%left COMMENT

%start rust_file expression ir_term toplevel_command maybe_toplevel_command 
%type <RustTerm.item list> rust_file
%type <RustTerm.expr> expression
%type <IrTerm.term> ir_term
%type <TopCmd.command> toplevel_command
%type <TopCmd.command option> maybe_toplevel_command
%%
rust_file:
| COMMENT rust_file { (RustTerm.Comment $1) :: $2 }
| fn_def rust_file { $1 :: $2 }
| EOF { [] }
; 
fn_def:
| FN IDENT LPARAN fn_args RPARAN block { RustTerm.FnDef { name = $2; args = $4; ret_type = Unit; body = $6 } }
| FN IDENT LPARAN fn_args RPARAN ARROW typ block { RustTerm.FnDef { name = $2; args = $4; ret_type = $7; body = $8 } }
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
| LPARAN RPARAN { Unit }
| INT_T { Int }
| FN LPARAN maybe_typs RPARAN ARROW typ { RustTerm.Fn ($3, $6) }
;
maybe_typs:
| typs { $1 }
| { [] }
;
typs:
| typ COMMA typs { $1 :: $3 }
| typ { $1 :: [] }
;     
statement:
| LET IDENT EQ expression { RustTerm.Let ($2, $4) }
| expression { Expr $1 }
statements:
| statement SEMICOLLON statements { $1 :: $3 }
| statement { [$1] }
| statement SEMICOLLON { [$1; RustTerm.Expr RustTerm.Nil] }
maybe_statements:
| { [] }
| statements { $1 }
block:                                 
| LBRACE maybe_statements RBRACE { $2 }
atom_expression:
| LPARAN RPARAN { RustTerm.Nil }
| IDENT { RustTerm.Variable $1 }
| INT { RustTerm.NumConst (int_of_string $1) }
| ifthenelse { $1 }
| atom_expression LPARAN maybe_expressions RPARAN { RustTerm.Call ($1, $3) }
| LPARAN expression RPARAN { $2 }
expression:
| atom_expression { $1 }
| expression PLUS expression { RustTerm.Add ($1, $3) }
| expression MINUS expression { RustTerm.Sub ($1, $3) }
| expression MULTIPLY atom_expression { RustTerm.Multiply ($1, $3) }
| expression DIVIDE expression { RustTerm.Divide ($1, $3) }
| expression LANGLE expression { RustTerm.Less ($1, $3) }
| expression RANGLE expression { RustTerm.Greater ($1, $3) }
| expression LANGLE_EQ expression { RustTerm.LessEqual ($1, $3) }
| expression RANGLE_EQ expression { RustTerm.GreaterEqual ($1, $3) }
| expression LONG_EQ expression { RustTerm.Equal ($1, $3) }
| MINUS expression %prec UMINUS { RustTerm.Negotiate $2 }
| block { RustTerm.Block $1 }
;
maybe_expressions:
| { [] }
| expressions { $1 }
expressions:
| expression COMMA expressions { $1 :: $3 }
| expression { $1 :: [] }
;
ifthenelse:
| IF expression block ELSE ifthenelse { RustTerm.IfThenElse ($2, $3, [RustTerm.Expr $5]) }
| IF expression block ELSE block { RustTerm.IfThenElse ($2, $3, $5) }
| IF expression block { RustTerm.IfThen ($2, $3) }
;

/*
effects:
| effect COMMA effects { $1 :: $3 }
| effect { [$1] }
effect:
| TOTAL { Total }
| DIVERGENT { Divergent }
| SPECIAL_IDENT { Varying $1 }
| MAX_EFFECT LPARAN effects RPARAN { Max $3 }
;
unwrapped_effectful_typ:
| LPARAN RPARAN { EUnit }
| INT_T { EInt }
| effect FN LPARAN maybe_unwrapped_effectful_typs RPARAN ARROW unwrapped_effectful_typ { EFn ($4, ($1, $7)) }
;
maybe_unwrapped_effectful_typs:
| unwrapped_effectful_typs { $1 }
| { [] }
;
unwrapped_effectful_typs:
| unwrapped_effectful_typ COMMA unwrapped_effectful_typs { $1 :: $3 }
| unwrapped_effectful_typ { $1 :: [] }
;
*/

ptr_list:
| FN_PTR { $1 :: [] }
| FN_PTR COMMA ptr_list { $1 :: $3 }
atom_ir_term:
| LPARAN ir_term RPARAN { $2 }
| IDENT { IrTerm.Var $1 }
| TOTAL { IrTerm.Total }
| DIVERGENT { IrTerm.Divergent }
| INT_T { IrTerm.IntegerType }
| INT { IrTerm.IntegerConst (int_of_string $1) }
| FN_PTR { IrTerm.FunctionPointer $1 }
| PROPOSITION { IrTerm.Proposition }
| TYPE { IrTerm.Type }
| PRE_TYPE { IrTerm.PreType } 
| KIND LSQBR INT RSQBR { IrTerm.Kind (int_of_string $3) }
| COMPUTATION_KIND { IrTerm.ComputationKind }
| PREDICATE { IrTerm.Predicate }
| atom_ir_term LANGLE ir_term RANGLE { IrTerm.ComputationType ($1, $3) }
| REC LSQBR ptr_list RSQBR LSQBR INT RSQBR { IrTerm.Recursion ($3, int_of_string $6) }
| MAX_COMP_KIND LPARAN ir_term COMMA ir_term RPARAN { IrTerm.MaxEffect ($3, $5) }
| AND_INTRO LPARAN ir_term COMMA ir_term RPARAN { IrTerm.AndIntroduction ($3, $5) }
| OR_INTRO_L LPARAN ir_term COMMA ir_term RPARAN { IrTerm.OrIntroductionL ($3, $5) }
| OR_INTRO_R LPARAN ir_term COMMA ir_term RPARAN { IrTerm.OrIntroductionR ($3, $5) }
| AND_ELIM_L LPARAN ir_term COMMA ir_term RPARAN { IrTerm.AndEliminationL ($3, $5) }
| AND_ELIM_R LPARAN ir_term COMMA ir_term RPARAN { IrTerm.AndEliminationR ($3, $5) }
| EQ_INTRO LPARAN ir_term COMMA ir_term RPARAN { IrTerm.EqIntro ($3, $5) }
| OR_ELIM LPARAN ir_term COMMA ir_term COMMA ir_term RPARAN { IrTerm.OrElimination ($3, $5, $7) }
| FN_PTR_TYPE LSQBR ir_term RSQBR { IrTerm.FnPtrType $3 }
| DEREF_FN_PTR LSQBR ir_term RSQBR { IrTerm.DerefFnPtr $3 }
| TRUTH { IrTerm.Truth }
| PROOF_OF_TRUTH { IrTerm.ProofOfTruth }
| FALSITY { IrTerm.Falsity }
| EQ_ELIM LPARAN ir_term COMMA ir_term COMMA ir_term RPARAN { IrTerm.EqElim ($3, $5, $7) }
| FALSE_ELIM_PROP LPARAN ir_term COMMA ir_term RPARAN { IrTerm.FalsityEliminationProposition ($3, $5) }
| FALSE_ELIM_TYPE LPARAN ir_term COMMA ir_term RPARAN { IrTerm.FalsityEliminationType ($3, $5) }
app_ir_term:
| app_ir_term atom_ir_term { IrTerm.App ($1, $2) }
| atom_ir_term { $1 }
arith_ir_term:
| app_ir_term { $1 }
| MINUS arith_ir_term %prec UMINUS { IrTerm.Opposite $2 }
| arith_ir_term PLUS arith_ir_term { IrTerm.Add ($1, $3) }
| arith_ir_term MINUS arith_ir_term { IrTerm.Subtract ($1, $3) }
| arith_ir_term MULTIPLY app_ir_term { IrTerm.Multiply ($1, $3) }
| arith_ir_term PROPOR arith_ir_term { IrTerm.Or ($1, $3) }
| arith_ir_term PROPAND app_ir_term { IrTerm.And ($1, $3) }
| FORALL IDENT COLLON ir_term DOT arith_ir_term %prec FORALL { IrTerm.Product ($2, $4, $6) }
| app_ir_term ARROW arith_ir_term %prec PROP_IMPLICATION { IrTerm.Product ("_", $1, $3) }
| arith_ir_term EQ arith_ir_term TYPE_HINT app_ir_term { IrTerm.Eq ($1, $3, $5) }
abs_ir_term:
| arith_ir_term { $1 }
| SLASH IDENT COLLON ir_term DOT abs_ir_term { IrTerm.Abs ($2, $4, $6) }
ir_term:
| abs_ir_term { $1 }
| abs_ir_term SEMICOLLON ir_term { IrTerm.Sequence ($1, $3) } 

def_arg:
| LPARAN IDENT COLLON ir_term RPARAN { ($2, $4) }
def_args:
| def_arg def_args { $1 :: $2 }
| def_arg { $1 :: [] }
toplevel_precommand:
| QUIT { TopCmd.Quit }
| RESET { TopCmd.Reset }
| AXIOM IDENT COLLON ir_term { TopCmd.Axiom ($2, $4) }
| TC_IR_TERM ir_term { TopCmd.TcIrTerm $2 }
| IR_DEFINITION IDENT def_args EQ ir_term { TopCmd.IrDefinition($2, $3, $5) } 
| IR_PRINT_DEFINITION IDENT { TopCmd.IrPrintDef $2 }
toplevel_command:
| toplevel_precommand DOT { $1 }
maybe_toplevel_command:
| toplevel_command { Some $1 }
| EOF { None }
