open Util

type const =
| Kind of int
| SmallType
| Prop

type dep_ty =
| Abs
| Prod
| Refine

(*
  TODO:
    we need Recursion. What should it be?
    - A recursion/induction schema for type?
    - Classical Y combinator?
  TODO:
    - we need assert/exception
*)
(* Special thanks to Komi Golov <3 *)
type 'a ir_term =
| Def of string
| Var of 'a
| Dep of { dep:dep_ty; mark:string; ty:'a ir_term; bod:'a ir_term }
| App of 'a ir_term * 'a ir_term
| Const of const

(*                                   Util                                           *)
(*==================================================================================*)

let fold_term c_def c_var c_const c_app c_dep shift (ctx : 'ctx) (acc : 'acc) term =
  let rec go ctx acc term =
    match term with
    | Def v -> c_def ctx acc v
    | Var v -> c_var ctx acc v
    | Const c -> c_const ctx acc c
    | App (l, r) ->
      let r_res = go ctx acc r in
      let l_res = go ctx r_res l in
      c_app ctx l_res r_res
    | Dep {dep; mark; ty; bod} ->
      let ty_res = go ctx acc ty in
      let bod_res = go (shift ctx ty_res dep mark) acc bod in
      c_dep ctx dep mark ty_res bod_res
  in
  go ctx acc term

let fmap_term m_def m_var m_const shift (ctx : 'ctx) term =
  let c_def ctx _ v = Def (m_def ctx v)
  and c_var ctx _ v = Var (m_var ctx v)
  and c_const ctx _ v = Const (m_const ctx v) in
  fold_term
    c_def
    c_var
    c_const
    (fun _ l r -> App (l, r))
    (fun _ dep mark ty bod -> Dep {dep; mark; ty; bod})
    shift
    ctx
    (Const Prop)
    term

(*                                   AST term                                       *)
(*==================================================================================*)

type ast_term = string ir_term

let stringify_const c =
  match c with
  | Kind k -> Printf.sprintf "Kind[%d]" k
  | SmallType -> "Small"
  | Prop -> "Prop"

let stringify_dep d mark ty bod =
  match d with
  | Abs -> Printf.sprintf "(/%s:%s.%s)" mark ty bod
  | Prod -> Printf.sprintf "(FOR %s:%s.%s)" mark ty bod
  | Refine -> Printf.sprintf "{%s:%s | %s}" mark ty bod

let stringify_ast t =
  fold_term
    (fun _ _ v -> v)
    (fun _ _ v -> v)
    (fun _ _ -> stringify_const)
    (fun _ -> Printf.sprintf "(%s %s)")
    (fun _ -> stringify_dep)
    (fun _ _ _ _ -> ())
    ()
    ""
    t

(*                                   De Brujin                                      *)
(*==================================================================================*)

type dbi = DeBruj of int
type db_ir_term = dbi ir_term

let stringify_de_bruj (t : db_ir_term) =
  fold_term
    (fun _ _ v -> v)
    (fun _ _ (DeBruj v) -> Printf.sprintf "REF[%d]" v)
    (fun _ _ -> stringify_const)
    (fun _ -> Printf.sprintf "(%s %s)")
    (fun _ -> stringify_dep)
    (fun _ _ _ _ -> ())
    ()
    ""
    t

let compile (nm : dbi StringMap.t) (term : ast_term) : db_ir_term =
  let append_var nm s =
    nm |> StringMap.map (fun (DeBruj x) -> (DeBruj (x + 1)))
       |> StringMap.add s (DeBruj 0)
  in
  fmap_term
    (fun _ v -> v)
    (fun nm s -> StringMap.find s nm)
    (fun _ c -> c)
    (fun nm _ _ s -> append_var nm s)
    nm
    term

let decompile (nm : string IntegerMap.t) (term : db_ir_term) : ast_term =
  let append_var nm s =
    nm |> IntegerMap.to_list
       |> List.map (fun (idx, s) -> (idx + 1, s))
       |> IntegerMap.of_list
       |> IntegerMap.add 0 s
  in
  fmap_term
    (fun _ v -> v)
    (fun nm (DeBruj i) -> IntegerMap.find i nm)
    (fun _ c -> c)
    (fun nm _ _ s -> append_var nm s)
    nm
    term

(* module type Variable =
  sig
    type t
  end

module type T =
  sig
    type var

  end

module Make(Var: Variable) : T with type var := Var.t = struct

end *)