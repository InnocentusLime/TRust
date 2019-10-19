/*
	Treat "S" more carefully
*/

%{
open PreIr
%}

%token LEMMA
%token WILDCARD
%token EOF
%token COMMA
%token SEMICOLLON
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
%token SLASH FORALL EXISTS
%token EQ
%token PROP_AND PROP_OR PROP_IMPLIES
%token TOP BOT
%token DOT
%token TYPE_HINT
%token UNIT BOOL NAT
%token BAR
%token LSQ RSQ
%token PROD
%token LANGLE RANGLE
%token SUBTYPE
%token PROP SMALL TYPE
%token NATREC BOOLREC SUMBOOLREC
%token CONVERT EXTRACT
%token MEMBERSHIP
%token SUBTRANS SUBPROD SUBREFL SUBSUB SUBGEN SUBUNREFINE
%token AMPERSAND
%token SBOOLL SBOOLR
%token OR_INTROL OR_INTROR
%token AND_INTRO
%token EQ_REFL
%token EXIST

%token APP ABS

%left APP
%left ABS
%left LPARAN LBRACE LSQ
%right PROD
%nonassoc SUBTYPE
%left PROP_AND
%left PROP_OR
%right FORALL ARROW 
%nonassoc DOT
%nonassoc EQ
%right COMMA
$nonassoc TYPE_HINT

%start lambda_term
%type <PreIr.term_ast> lambda_term
%%

const:
| NIL { Nil }
| ZERO { NatO }
| SUCC { NatSucc }
| FALSE { BoolFalse }
| TRUE { BoolTrue }
| VAR { Var $1 }
| NAT { Nat }
| BOOL { Bool }
| UNIT { Unit }
| PROP { Prop }
| SMALL { Small }
| TYPE LSQ INT RSQ { Type $3 }
term:
| term EQ term TYPE_HINT term { Eq ($1, $3, $5) }
| atom_term ARROW term { Forall ("_", $1, $3) }
| term PROP_AND term { Conjunction ($1, $3) }
| term PROP_OR term { Disjunction ($1, $3) }
| LSQ term RSQ AMPERSAND LSQ term RSQ { Sumbool ($2, $6) }
| app_term %prec APP { $1 }
| SLASH VAR COLLON term DOT term %prec ABS { Abs ($2, $4, $6) }
| SLASH WILDCARD COLLON term DOT term %prec ABS { Abs ("_", $4, $6) }
| FORALL VAR COLLON term DOT term { Forall ($2, $4, $6) }
| FORALL WILDCARD COLLON term DOT term { Forall ("_", $4, $6) }
| EXISTS VAR COLLON term DOT term { Exists ($2, $4, $6) }
| atom_term SUBTYPE atom_term { Subtyping ($1, $3) }
atom_term:
| EQ_REFL LPARAN term SEMICOLLON term RPARAN { EqRefl ($3, $5) }
| SUBTRANS LPARAN term SEMICOLLON term SEMICOLLON term SEMICOLLON term SEMICOLLON term RPARAN { SubTrans ($3, $5, $7, $9, $11) }
| SUBPROD LPARAN term SEMICOLLON term SEMICOLLON term SEMICOLLON term SEMICOLLON term SEMICOLLON term RPARAN { SubProd ($3, $5, $7, $9, $11, $13) }
| SUBREFL LPARAN term RPARAN { SubRefl $3 }
| SUBSUB LPARAN term SEMICOLLON term SEMICOLLON term SEMICOLLON term RPARAN { SubSub ($3, $5, $7, $9) }
| SBOOLL LPARAN term SEMICOLLON term RPARAN { SBLeft ($3, $5) }   // proof, prop
| SBOOLR LPARAN term SEMICOLLON term RPARAN { SBRight ($3, $5) }  // prop, proof
| SUBUNREFINE LPARAN term SEMICOLLON term RPARAN { SubUnrefine ($3, $5) }
| SUBGEN LPARAN term SEMICOLLON term SEMICOLLON term RPARAN { SubGen ($3, $5, $7) }
| MEMBERSHIP LPARAN term SEMICOLLON term SEMICOLLON term SEMICOLLON term RPARAN { Membership ($3, $5, $7, $9) }
| NATREC LPARAN term SEMICOLLON term SEMICOLLON term SEMICOLLON term RPARAN { NatRec ($3, $5, $7, $9) }
| BOOLREC LPARAN term SEMICOLLON term SEMICOLLON term SEMICOLLON term RPARAN { BoolRec ($3, $5, $7, $9) }
| SUMBOOLREC LPARAN term SEMICOLLON term SEMICOLLON term SEMICOLLON term SEMICOLLON term SEMICOLLON term RPARAN { SumboolRec ($3, $5, $7, $9, $11, $13) }
| const { $1 }
| LBRACE term BAR term RBRACE { Refine ($2, $4) }
| LPARAN term RPARAN { $2 }
| LSQ term BAR term RSQ { Sumbool ($2, $4) }
| EXIST LPARAN term SEMICOLLON term SEMICOLLON term SEMICOLLON term RPARAN { Exist ($3, $5, $7, $9) }
| OR_INTROL LPARAN term SEMICOLLON term SEMICOLLON term RPARAN { OrIntroL ($3, $5, $7) }
| OR_INTROR LPARAN term SEMICOLLON term SEMICOLLON term RPARAN { OrIntroR ($3, $5, $7) }
| AND_INTRO LPARAN term SEMICOLLON term SEMICOLLON term SEMICOLLON term RPARAN { AndIntro ($3, $5, $7, $9) }
app_term:
| atom_term { $1 }
| app_term atom_term { App ($1, $2) }
lambda_term:
| term EOF { $1 }


