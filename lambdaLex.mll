{
	open LambdaAst;;
	let keyword_table = (
		let temp = Hashtbl.create 2 in
		(
			Hashtbl.add temp "natRec" NATREC;
			Hashtbl.add temp "sumboolRec" SUMBOOLREC;
			Hashtbl.add temp "boolRec" BOOLREC; 
			Hashtbl.add temp "nat" NAT;
			Hashtbl.add temp "unit" UNIT;
			Hashtbl.add temp "bool" BOOL;
			Hashtbl.add temp "false" FALSE;
			Hashtbl.add temp "true" TRUE;
			Hashtbl.add temp "nil" NIL;
			Hashtbl.add temp "S" SUCC;
			Hashtbl.add temp "forall" FORALL;
			Hashtbl.add temp "exists" EXISTS;
			Hashtbl.add temp "TRUE" TOP;
			Hashtbl.add temp "FALSE" BOT; 
			Hashtbl.add temp "lemma" LEMMA;
			Hashtbl.add temp "small" SMALL;
			Hashtbl.add temp "type" TYPE;
			Hashtbl.add temp "prop" PROP;
			Hashtbl.add temp "trans" SUBTRANS;
			Hashtbl.add temp "prod" SUBPROD;
			Hashtbl.add temp "sub" SUBSUB;
			Hashtbl.add temp "gen" SUBGEN;
			Hashtbl.add temp "unrefine" SUBUNREFINE;
			Hashtbl.add temp "membership" MEMBERSHIP;
			Hashtbl.add temp "refl" SUBREFL;
			Hashtbl.add temp "sboolL" SBOOLL;
			Hashtbl.add temp "sboolR" SBOOLR;
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
let newline = ['\r' '\n']

let ident = (letter (alpha_num*)) | ('_' (alpha_num+))

rule lex =
parse
| ";" { SEMICOLLON }
| "_" { WILDCARD }
| "*" { PROD }
| "<" { LANGLE }
| "&" { AMPERSAND }
| ":>" { TYPE_HINT }
| "<:" { SUBTYPE }
| ">" { RANGLE }
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
| "/" { SLASH }
| (space | newline) { lex lexbuf }
| ident as s { if Hashtbl.mem keyword_table s then Hashtbl.find keyword_table s else VAR s }
| (number)+ as s { INT (int_of_string s) }
| "==" { EQ }
| "," { COMMA } 
| '.' { DOT }
| ':' { COLLON }
| eof { EOF }