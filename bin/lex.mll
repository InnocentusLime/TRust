{
  open Ast

  let keyword_table = (
    let temp = Hashtbl.create 256 in
    Hashtbl.add temp "let" LET;
    Hashtbl.add temp "if" IF; 
    Hashtbl.add temp "else" ELSE; 
    Hashtbl.add temp "fn" FN; 
    Hashtbl.add temp "int" INT_T;
    Hashtbl.add temp "Falsity" FALSITY;
    Hashtbl.add temp "Truth" TRUTH;
    Hashtbl.add temp "total" TOTAL;
    Hashtbl.add temp "divergent" DIVERGENT;
    Hashtbl.add temp "forall" FORALL;
    Hashtbl.add temp "Prop" PROPOSITION;
    Hashtbl.add temp "Type" TYPE;
    Hashtbl.add temp "Predicate" PREDICATE;
    Hashtbl.add temp "TypeBuilder" TYPE_BUILDER;
    Hashtbl.add temp "PreType" PRE_TYPE;
    Hashtbl.add temp "Kind" KIND;
    Hashtbl.add temp "CompKind" COMPUTATION_KIND;
    Hashtbl.add temp "rec" REC; 
    Hashtbl.add temp "max_comp_kind" MAX_COMP_KIND;
    Hashtbl.add temp "and_intro" AND_INTRO;
    Hashtbl.add temp "or_intro_l" OR_INTRO_L;
    Hashtbl.add temp "or_intro_r" OR_INTRO_R;
    Hashtbl.add temp "or_elim" OR_ELIM;
    Hashtbl.add temp "and_elim_l" AND_ELIM_L;
    Hashtbl.add temp "and_elim_r" AND_ELIM_R;
    Hashtbl.add temp "eq_intro" EQ_INTRO;
    Hashtbl.add temp "FNPTR" FN_PTR_TYPE;
    Hashtbl.add temp "DEREF" DEREF_FN_PTR;
    Hashtbl.add temp "Truth" TRUTH;
    Hashtbl.add temp "truth" PROOF_OF_TRUTH;
    Hashtbl.add temp "Falsity" FALSITY;
    Hashtbl.add temp "eq_elim" EQ_ELIM;
    Hashtbl.add temp "false_elim_prop" FALSE_ELIM_PROP;
    Hashtbl.add temp "false_elim_type" FALSE_ELIM_TYPE;
    Hashtbl.add temp "true" BOOL_TRUE;
    Hashtbl.add temp "false" BOOL_FALSE;
    Hashtbl.add temp "bool" BOOL_TYPE;
    
    Hashtbl.add temp "reset" RESET;
    Hashtbl.add temp "quit" QUIT;
    Hashtbl.add temp "axiom" AXIOM;
    Hashtbl.add temp "tc_ir_term" TC_IR_TERM;
    Hashtbl.add temp "ir_def" IR_DEFINITION;
    Hashtbl.add temp "ir_print_def" IR_PRINT_DEFINITION;
    Hashtbl.add temp "ir_is_conv" IR_IS_CONV;
    Hashtbl.add temp "ir_simpl" IR_SIMPL;
    Hashtbl.add temp "ir_load_mod" IR_LOAD_MOD;
    temp
  )

  let special_keyword_table = (
    let temp = Hashtbl.create 256 in
    temp
  )
}

let lower_letter = ['a' - 'z']
let upper_letter = ['A' - 'Z']
let letter = lower_letter | upper_letter
let number = ['0' - '9']
let alpha_num  = letter | number | '_'
let space = ['\t' ' ']
let newline = '\n'

let ident = (letter (alpha_num*)) | ('_'+ letter (alpha_num+))

rule lex =
parse          
| "\"" (([^'"'])+ as s) "\"" { STRING s } 
| "=>" { FATARROW }
| "\\/" { PROPOR }
| "/\\" { PROPAND }
| ("//" (([^'\n'])* as s) newline) { COMMENT s }
| ("/*" ((_*) as s) "*/") { COMMENT s }
| (space | newline) { lex lexbuf }
| number+ as n { INT n }
| '-' number+ as n { INT n }
| '@' (ident as s) { FN_PTR s }
| '\'' (ident as s) { if Hashtbl.mem special_keyword_table s then Hashtbl.find special_keyword_table s else SPECIAL_IDENT s }
| ident as s { if Hashtbl.mem keyword_table s then Hashtbl.find keyword_table s else IDENT s }
| "===" { PROPEQ }
| ":>" { TYPE_HINT }
| "@" { AT }
| "->" { ARROW }
| "<=" { LANGLE_EQ }
| ">=" { RANGLE_EQ }
| "==" { LONG_EQ }
| '<' { LANGLE }
| '>' { RANGLE }
| '+' { PLUS }
| '-' { MINUS }
| '/' { DIVIDE }
| '*' { MULTIPLY }
| '(' { LPARAN }
| ')' { RPARAN }
| '{' { LBRACE }
| '}' { RBRACE }
| '[' { LSQBR }
| ']' { RSQBR }
| ',' { COMMA }
| ';' { SEMICOLLON }
| ':' { COLLON }
| '=' { EQ }
| '.' { DOT }
| '\\' { SLASH }
| eof { EOF }
