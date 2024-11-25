open Util

type const =
| Kind of int
| SmallType
| Prop

type dep_ty =
| Abs
| Prod
| Refine

type 'a ir_term =
| Def of string
| Var of 'a
| Dep of { dep:dep_ty; mark:string; ty:'a ir_term; bod:'a ir_term }
| App of 'a ir_term * 'a ir_term
| Const of const

type dbi = DeBruj of int

type ast_term = string ir_term
type db_ir_term = dbi ir_term

val fold_term :
  ('ctx -> 'acc -> string -> 'acc) ->
  ('ctx -> 'acc -> 'a -> 'acc) ->
  ('ctx -> 'acc -> const -> 'acc) ->
  ('ctx -> 'acc -> 'acc -> 'acc) ->
  ('ctx -> dep_ty -> string -> 'acc -> 'acc -> 'acc) ->
  ('ctx -> 'acc -> dep_ty -> string -> 'ctx) ->
    'ctx -> 'acc -> 'a ir_term -> 'acc

val fmap_term :
  ('ctx -> string -> string) ->
  ('ctx -> 'a -> 'b) ->
  ('ctx -> const -> const) ->
  ('ctx -> 'b ir_term -> dep_ty -> string -> 'ctx) ->
    'ctx -> 'a ir_term -> 'b ir_term

val stringify_ast : ast_term -> string

val stringify_de_bruj : db_ir_term -> string

val compile : dbi StringMap.t -> ast_term -> db_ir_term

val decompile : string IntegerMap.t -> db_ir_term -> ast_term