open LambdaLex;;
open LambdaAst;;

let parse_top_level_string str = top_level_command lex (Lexing.from_string str);;