
type expr =
| Nil
| Variable of string
| NumConst of int
| Call of expr * (expr list) 
| Add of expr * expr
| Sub of expr * expr
| Multiply of expr * expr
| Divide of expr * expr
| Less of expr * expr
| Greater of expr * expr
| LessEqual of expr * expr
| GreaterEqual of expr * expr
| Equal of expr * expr
| Negotiate of expr
| IfThenElse of expr * block * block
| IfThen of expr * block
| Block of block
and statement =
| Let of string * expr
| Expr of expr
and block = statement list 

type typ =
| Unit
| Int
| Fn of (typ list) * typ

type arg = string * typ

type fn_def =
{
  name : string;
  args : arg list;
  ret_type : typ;
  body : block;
}

type item =      
| Comment of string
| FnDef of fn_def

