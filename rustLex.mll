{
	open RustAst;;
	let keyword_table = (
		let temp = Hashtbl.create 2 in
		(
			Hashtbl.add temp "if" IF; 
			Hashtbl.add temp "else" ELSE; 
			Hashtbl.add temp "fn" FN; 
			Hashtbl.add temp "int" INT_T;
			Hashtbl.add temp "Pure" PURE;
			Hashtbl.add temp "Div" DIV;
			Hashtbl.add temp "with" WITH;
			Hashtbl.add temp "val" VAL;
			Hashtbl.add temp "prove_termination" PROVE_TERMINATION;
			Hashtbl.add temp "unit" UNIT_T; 
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
| "=>" { FATARROW }
| "\\/" { PROPOR }
| "/\\" { PROPAND }
| "()" { UNIT }
| ("//" ((alpha_num | space)* as s) newline) { COMMENT s }
| ("/*" ((alpha_num | space | newline)* as s) "*/") { COMMENT s }
| (space | newline) { lex lexbuf }
| number+ as n { INT n }
| ident as s { if Hashtbl.mem keyword_table s then Hashtbl.find keyword_table s else IDENT s }
| "===" { PROPEQ } 
| "->" { ARROW }
| "<=" { LANGLE_EQ }
| ">=" { RANGLE_EQ }
| "==" { EQ }
| '<' { LANGLE }
| '>' { RANGLE }
| '+' { PLUS }
| '-' { MINUS }
| '/' { DIVIDE }
| '*' { MULTIPLY }
| '(' { LPAREN }
| ')' { RPAREN }
| '{' { LBRACE }
| '}' { RBRACE }
| ',' { COMMA }
| ':' { COLLON }
| eof { EOF }