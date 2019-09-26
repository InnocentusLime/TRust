{
	open LambdaAst;;
	let keyword_table = (
		let temp = Hashtbl.create 2 in
		(
			Hashtbl.add temp "for" FOR;
			Hashtbl.add temp "do" DO;
			Hashtbl.add temp "if" IF; 
			Hashtbl.add temp "else" ELSE;
			Hashtbl.add temp "then" THEN; 
			Hashtbl.add temp "nat" NAT;
			Hashtbl.add temp "unit" UNIT;
			Hashtbl.add temp "bool" BOOL;
			Hashtbl.add temp "false" FALSE;
			Hashtbl.add temp "true" TRUE;
			Hashtbl.add temp "nil" NIL;
			Hashtbl.add temp "succ" SUCC;
			Hashtbl.add temp "forall" FORALL;
			Hashtbl.add temp "exists" EXISTS;
			Hashtbl.add temp "TRUE" TOP;
			Hashtbl.add temp "FALSE" BOT; 
			temp
		)
	);;
}

let lower_letter = ['a' - 'z']
let upper_letter = ['A' - 'Z']
let letter = lower_letter | upper_letter
let number = ['0' - '9']
let alpha_num  = letter | number
let space = ['\t' ' ']
let newline = '\n'

let ident = (letter (alpha_num*)) | ('_' (alpha_num+))

rule lex =
parse
| "*" { PROD }
| "<" { LANGLE }
| ">" { RANGLE }
| ":>" { TYPE_HINT }
| "O" { ZERO }
| "(" { LPARAN }
| ")" { RPARAN }
| "{" { LBRACE }
| "}" { RBRACE }
| "[" { LSQ }
| "]" { RSQ }
| "|" { BAR }
| "\\/" { PROP_OR }
| "/\\" { PROP_AND }
| "->" { ARROW }
| "=>" { FAT_ARROW }
| "/" { SLASH }
| (space | newline) { lex lexbuf }
| ident as s { if Hashtbl.mem keyword_table s then Hashtbl.find keyword_table s else VAR s }
| (number)+ as s { INT (int_of_string s) }
| "==" { EQ }
| "," { COMMA } 
| '.' { DOT }
| ':' { COLLON }
| eof { EOF }