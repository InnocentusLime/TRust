let cut_list l n =
  let rec cut_list' cut_part rest n =
    match (rest, n) with
    | (_, 0) -> (cut_part, rest)
    | (h :: t, _) -> cut_list' (h :: cut_part) t (n - 1)
    | ([], _) -> failwith "the list ended too early"
  in
  cut_list' [] l n |> fun (l, r) -> (List.rev l, r)

let list_pop l n =
  let leng = List.length l in
  fst (cut_list l (leng - n))

let rec set_list_elem l i x =
  match (l, i) with
  | ([], _) -> failwith "index out of range"
  | (_ :: t, 0) -> x :: t
  | (h :: t, i) -> h :: set_list_elem t (i - 1) x

let is_list_of_equal_items l =
        match l with
        | [] -> true
        | h :: t -> List.for_all (fun x -> x = h) t

type typ =
| Unit
| Bool
| Fn of (typ list) * typ
| RecGroup of (typ list) * typ
| RefType of typ
| Int

(* The information about a memeory cell *)
type mem_cell =
| Known of int   (* This memory cell was allocated by us *)
| Stack of int   (* We reference the stack *)

type const =
| Nil
| BoolTrue
| BoolFalse
| NumConst of int
| FnPtr of int
| Ref of mem_cell
| Rec of (int list) * int (* Rec [pointers to bodies] [index of chosen alias] *)
| Var of int

type expr =
| Const of const
| ConstRef of int
| And of expr * expr
| Or of expr * expr
| Not of expr
| Call of expr * (expr list)
| Block of block
| Equal of expr * expr
| Write of expr * expr
| MoveStackVar of int
| Add of expr * expr
| Sub of expr * expr
| Divide of expr * expr
| Multiply of expr * expr
| Negotiate of expr
| Greater of expr * expr
| Less of expr * expr
| LessEqual of expr * expr
| GreaterEqual of expr * expr
| IfThenElse of expr * block * block
| MoveOutOfRef of expr
and stmt =
| Expr of expr
| Let of string * expr
(* In Rust variables get popped when we leave the block. Each block keeps a number which indicates how many values to pop of stack *)
and block = (stmt list * int)

let same_const l r = (l = r)

let rec same_expr l r =
  match (l, r) with
  | (Const l, Const r) -> same_const l r
  | (ConstRef l, ConstRef r) | (MoveStackVar l, MoveStackVar r) -> l = r
  | (And (xl, yl), And (xr, yr)) | (Or (xl, yl), Or (xr, yr)) | (Add (xl, yl), Add (xr, yr))
  | (Sub (xl, yl), Sub (xr, yr)) | (Divide (xl, yl), Divide (xr, yr)) | (Multiply (xl, yl), Multiply (xr, yr))
  | (Greater (xl, yl), Greater (xr, yr)) | (Less (xl, yl), Less (xr, yr)) | (LessEqual (xl, yl), LessEqual (xr, yr))
  | (GreaterEqual (xl, yl), GreaterEqual (xr, yr)) | (Equal (xl, yl), Equal (xr, yr)) | (Write (xl, yl), Write (xr, yr))
    -> same_expr xl xr && same_expr yl yr
  | (IfThenElse (condl, on_truel, on_falsel), IfThenElse (condr, on_truer, on_falser)) ->
    same_expr condl condr && same_block on_truel on_truer && same_block on_falsel on_falser
  | (Not l, Not r) | (MoveOutOfRef l, MoveOutOfRef r) | (Negotiate l, Negotiate r) -> same_expr l r
  | (Call (calleel, argsl), Call (calleer, argsr)) -> (
    if List.length argsl = List.length argsr then same_expr calleel calleer && List.for_all2 same_expr argsl argsr
    else false
  )
  | (Block l, Block r) -> same_block l r
  | _ -> false
and same_stmt l r =
  match (l, r) with
  | (Expr l, Expr r) -> same_expr l r
  | (Let (_, l), Let (_, r)) -> same_expr l r
  | _ -> false
and same_block (l, _) (r, _) =
  if List.length l = List.length r then List.for_all2 same_stmt l r
  else false

type func =
{
  name : string;
  args : (string * typ) list;
  ret_type : typ;
  body : block;
}

let same_func l r = List.for_all2 (=) l.args r.args && l.ret_type = r.ret_type && same_block l.body r.body

let rec string_of_typ t =
  match t with
  | Int -> "int"
  | Unit -> "unit"
  | Bool -> "bool"
  | RefType x -> Printf.sprintf "&%s" (string_of_typ x)
  | Fn (args, ret) -> Printf.sprintf "(%s -> %s)" (args |> List.map string_of_typ |> String.concat " -> ") (string_of_typ ret)
  | RecGroup (args, ret) -> Printf.sprintf "REC(%s -> %s)" (args |> List.map string_of_typ |> String.concat " -> ") (string_of_typ ret)

let string_of_mem_cell m =
  match m with
  | Known x -> Printf.sprintf "&%d" x
  | Stack x -> Printf.sprintf "#%d" x

let string_of_const c =
  match c with
  | Nil -> "NIL"
  | BoolTrue -> "TRUE"
  | BoolFalse -> "FALSE"
  | NumConst x -> Printf.sprintf "@INT[%d]" x
  | FnPtr x -> Printf.sprintf "@FUNC[%d]" x
  | Ref cell -> string_of_mem_cell cell
  | Rec (bodies, chosen) -> Printf.sprintf "@REC[(%s), %d]" (bodies |> List.map (Printf.sprintf "%d") |> String.concat ", ") chosen
  | Var x -> Printf.sprintf "VAR%%%d" x

let rec string_of_expr e =
  match e with
  | Const c -> string_of_const c
  | ConstRef i -> Printf.sprintf "@CONST[%d]" i
  | And (l, r) -> Printf.sprintf "(&& %s %s)" (string_of_expr l) (string_of_expr r)
  | Or (l, r) -> Printf.sprintf "(|| %s %s)" (string_of_expr l) (string_of_expr r)
  | Not x -> Printf.sprintf "(! %s)" (string_of_expr x)
  | Call (callee, args) -> Printf.sprintf "(%s %s)" (string_of_expr callee) (args |> List.map string_of_expr |> String.concat " ")
  | Block b -> string_of_block b
  | Equal (l, r) -> Printf.sprintf "(== %s %s)" (string_of_expr l) (string_of_expr r)
  | Write (target, what) -> Printf.sprintf "(@WRITE %s %s)" (string_of_expr target) (string_of_expr what)
  | MoveStackVar m -> Printf.sprintf "@MOVE_STACK_VAR[#%d]" m
  | Add (l, r) -> Printf.sprintf "(+ %s %s)" (string_of_expr l) (string_of_expr r)
  | Sub (l, r) -> Printf.sprintf "(- %s %s)" (string_of_expr l) (string_of_expr r)
  | Divide (l, r) -> Printf.sprintf "(/ %s %s)" (string_of_expr l) (string_of_expr r)
  | Multiply (l, r) -> Printf.sprintf "(* %s %s)" (string_of_expr l) (string_of_expr r)
  | Negotiate x -> Printf.sprintf "(- %s)" (string_of_expr x)
  | Greater (l, r) -> Printf.sprintf "(> %s %s)" (string_of_expr l) (string_of_expr r)
  | Less (l, r) -> Printf.sprintf "(< %s %s)" (string_of_expr l) (string_of_expr r)
  | LessEqual (l, r) -> Printf.sprintf "(<= %s %s)" (string_of_expr l) (string_of_expr r)
  | GreaterEqual (l, r) -> Printf.sprintf "(>= %s %s)" (string_of_expr l) (string_of_expr r)
  | IfThenElse (cond, on_true, on_false) -> Printf.sprintf "@ITE[%s]%s%s" (string_of_expr cond) (string_of_block on_true) (string_of_block on_false)
  | MoveOutOfRef x -> Printf.sprintf "(@MOVE_OUT_OF_REF %S)" (string_of_expr x)
and string_of_stmt s =
  match s with
  | Expr e -> string_of_expr e
  | Let (name, e) -> Printf.sprintf "PUSH[%s, %s]" name (string_of_expr e)
and string_of_block (b, n) = b |> List.map string_of_stmt |> String.concat "; " |> Printf.sprintf "[%d]{%s}" n

let string_of_func f =
  Printf.sprintf "def %s : %s -> %s := %s"
  f.name
  (
    f.args |>
    List.map (fun (name, typ) -> Printf.sprintf "(%s:%s)" name (string_of_typ typ)) |>
    String.concat " -> "
  )
  (string_of_typ f.ret_type)
  (string_of_block f.body)

type typing_ctx =
{
  stack : (string * typ) list;
  consts : (string * typ * const) list;
  lib : func list;
  mem : typ list;
  vars : (string * typ) list;
}

let string_of_typing_ctx ctx =
  Printf.sprintf "{\n[%s]\n[%s]\n[%s]\n[%s]\n[%s]\n}"
  (ctx.stack |> List.map (fun (s, t) -> Printf.sprintf "%s : %s" s (string_of_typ t)) |> String.concat ", ")
  (ctx.consts |> List.map (fun (s, t, c) -> Printf.sprintf "%s : %s := %s" s (string_of_typ t) (string_of_const c)) |> String.concat ", ")
  (ctx.lib |> List.map (fun f -> Printf.sprintf "\n%s\n" (string_of_func f)) |> String.concat ";;")
  (ctx.mem |> List.map string_of_typ |> String.concat ", ")
  (ctx.vars |> List.map (fun (s, t) -> Printf.sprintf "%s : %s" s (string_of_typ t)) |> String.concat ", ")

let empty_ctx =
  {
    stack = [];
    consts = [];
    lib = [];
    mem = [];
    vars = [];
  }

let add_cell_to_context ctx v =
  {
    stack = ctx.stack;
    consts = ctx.consts;
    lib = ctx.lib;
    mem = ctx.mem @ [v];
    vars = ctx.vars;
  }

let add_func_to_context_lib ctx v =
  {
    stack = ctx.stack;
    consts = ctx.consts;
    lib = ctx.lib @ [v];
    mem = ctx.mem;
    vars = ctx.vars;
  }

let push_variable_to_context_stack ctx v =
  {
    stack = ctx.stack @ [v];
    consts = ctx.consts;
    lib = ctx.lib;
    mem = ctx.mem;
    vars = ctx.vars;
  }

let infer_type_fn_ptr ctx v = v |> List.nth ctx.lib |> fun f -> Fn (List.map snd f.args, f.ret_type)
let infer_type_known_mem_cell ctx v = ctx.mem |> fun l -> List.nth l v
let infer_type_stack ctx v = ctx.stack |> (fun l -> List.nth l (List.length l - v - 1)) |> snd
let infer_type_var ctx v = ctx.vars |> (fun l -> List.nth l v) |> snd

(*
 Looks up the body's signature and returns the following information
 1. the types of the mutually recursive bodies
 2. the type of the body which will be visible to other bodies
*)
let fetch_body_info body_count body_type =
  match body_type with
  | Fn (args, ret_type) -> (
    let (mutual_bodies_types, actual_args) = cut_list args body_count in
    (mutual_bodies_types, RecGroup (actual_args, ret_type))
  )
  | _ -> failwith "the body is not a function"
(*
 All functions must reference the same functions in the mutual recursion
 in the same order. This method ensures that.
*)
let collect_body_types input =
  let (bodies, func_data) = input |> List.split in
  if not (is_list_of_equal_items bodies) then failwith "recursor mismatch";
  (List.hd bodies, func_data)

let infer_type_const ctx c =
  match c with
  | Nil -> Unit
  | NumConst _ -> Int
  | BoolTrue | BoolFalse -> Bool
  | Ref (Stack x) -> infer_type_stack ctx x
  | Ref (Known x) -> infer_type_known_mem_cell ctx x
  | FnPtr address -> infer_type_fn_ptr ctx address
  | Rec (bodies, i) -> (
    if bodies = [] then failwith "Rec can't have zero bodies";
      let body_count = List.length bodies in
      let (body_typ_list, func_signatures) =
        bodies |>
        List.map (
          fun x ->
            x |> infer_type_fn_ptr ctx |>
            fetch_body_info body_count
        ) |>
        collect_body_types
      in
      let answer = List.nth func_signatures i in
      if List.nth body_typ_list i <> answer then failwith "Recursor signature mismatch";
      answer
  )
  | Var x -> infer_type_var ctx x

let rec infer_type_expr ctx e =
  match e with
  | Const c -> infer_type_const ctx c
  | ConstRef i -> List.nth ctx.consts i |> fun (_, t, _) -> t
  | And (l, r) | Or (l, r) -> (
    if infer_type_expr ctx l <> Bool then failwith "expected bool";
    if infer_type_expr ctx r <> Bool then failwith "expected bool";
    Bool
  )
  | Not x -> (
    if infer_type_expr ctx x <> Bool then failwith "expected bool";
    Bool
  )
  | Call (callee, args) -> (
                let arg_types = args |> List.map (infer_type_expr ctx) in
                match infer_type_expr ctx callee with
                | Fn (expected_arg_types, ret_type) -> (
                  if expected_arg_types = arg_types then ret_type
                  else failwith "argument types mismatch in a call"
                )
                | RecGroup (expected_arg_types, ret_type) -> (
                  if expected_arg_types = arg_types then ret_type
                  else failwith "argument types mismatch in a call"
                )
                | _ -> failwith "callee doesn't have a function type"
        )
        | Block b -> infer_type_block ctx b
        | Equal (l, r) -> (
                let l_type = infer_type_expr ctx l
                and r_type = infer_type_expr ctx r in
                if l_type <> r_type then failwith "compared values have different types";
                match l_type with
                | Bool | Unit | Fn (_, _) | RefType _ | Int -> Bool
                | _ -> failwith "the type of values you want to compare doesn't implement `Eq`"
        )
        | Write (target, value) -> (
                let target_type = infer_type_expr ctx target
                and value_type = infer_type_expr ctx value in
                match target_type with
                | RefType reffed_type when reffed_type = value_type -> Unit
                | _ -> failwith "the value type doesn't match the type of reference"
        )
        | MoveStackVar from -> infer_type_stack ctx from
        | Add (l, r) | Sub (l, r) | Multiply (l, r) | Divide (l, r) -> (
          if infer_type_expr ctx l = Int && infer_type_expr ctx r = Int then Int
          else failwith "One of the sides is not an Int"
        )
        | Negotiate x -> (
          if infer_type_expr ctx x = Int then Int
          else failwith "The negotiated expr is not an Int"
        )
        | Less (l, r) | Greater (l, r) | LessEqual (l, r) | GreaterEqual (l, r) -> (
          if infer_type_expr ctx l = Int && infer_type_expr ctx r = Int then Bool
          else failwith "One of the sides is not an Int"
        )
        | IfThenElse (cond, on_true, on_false) -> (
          let on_false_type = infer_type_block ctx on_false in
          if infer_type_expr ctx cond = Bool && infer_type_block ctx on_true = on_false_type then on_false_type
          else failwith "The if branches have different types"
        )
        | MoveOutOfRef x -> (
          match infer_type_expr ctx x with
          | RefType t -> t
          | _ -> failwith "@MOVE_OUT_OF_REF requires a reference"
        )
and infer_type_stmt ctx s =
  match s with
  | Let (id, e) -> (
    let typ = infer_type_expr ctx e in
    (push_variable_to_context_stack ctx (id, typ), Unit)
  )
  | Expr e -> (ctx, infer_type_expr ctx e)
and infer_type_block ctx (b, _) =
  List.fold_left
  (
    fun (ctx, _) x ->
    infer_type_stmt ctx x
  ) (ctx, Unit) b |> snd

(*
  This function adds newly compiled input to the context. Type checking happens in
  the process.
*)
let load_module ctx input =
  List.fold_left
  (
    fun ctx f ->
    let body_ctx = List.fold_left push_variable_to_context_stack ctx f.args in
    let body_typ = infer_type_block body_ctx f.body in
    if body_typ = f.ret_type then (
      Printf.printf "%s loaded\n" f.name; add_func_to_context_lib ctx f
    ) else failwith "The body type mismatches the return type"
  ) ctx input

let is_expr_const e =
  match e with
  | BoolTrue | BoolFalse | NumConst _ | Nil -> true
  | _ -> false

type master_ctx =
{
  stack : (string * typ * const) list;
  consts : (string * typ * const) list;
  lib : func list;
  mem : (const * typ) list;
  vars : (string * typ) list;
}

let string_of_master_ctx ctx =
  Printf.sprintf "{\n[%s]\n[%s]\n[%s]\n[%s]\n[%s]\n}"
  (ctx.stack |> List.map (fun (s, t, c) -> Printf.sprintf "%s : %s := %s" s (string_of_typ t) (string_of_const c)) |> String.concat ", ")
  (ctx.consts |> List.map (fun (s, t, c) -> Printf.sprintf "%s : %s := %s" s (string_of_typ t) (string_of_const c)) |> String.concat ", ")
  (ctx.lib |> List.map (fun f -> Printf.sprintf "\n%s\n" (string_of_func f)) |> String.concat ";;")
  (ctx.mem |> List.map (fun (c, t) -> Printf.sprintf "%s : %s" (string_of_const c) (string_of_typ t)) |> String.concat ", ")
  (ctx.vars |> List.map (fun (s, t) -> Printf.sprintf "%s : %s" s (string_of_typ t)) |> String.concat ", ")

let same_master_ctx l r =
  if
    List.length l.stack = List.length r.stack &&
    List.length l.consts = List.length r.consts &&
    List.length l.lib = List.length r.lib &&
    List.length l.mem = List.length r.mem &&
    List.length l.vars = List.length r.vars
  then (
    List.for_all2 (fun (_, l_t, l_c) (_, r_t, r_c) -> l_t = r_t && same_const l_c r_c) l.stack r.stack &&
    List.for_all2 (fun (_, l_t, l_c) (_, r_t, r_c) -> l_t = r_t && same_const l_c r_c) l.consts r.consts &&
    List.for_all2 same_func l.lib r.lib &&
    List.for_all2 (fun (l_c, l_t) (r_c, r_t) -> same_const l_c r_c && l_t = r_t) r.mem l.mem &&
    List.for_all2 (fun (_, l_t) (_, r_t) -> l_t = r_t) l.vars r.vars
  ) else false

let empty_master_ctx =
{
  stack = [];
  consts = [];
  lib = [];
  mem = [];
  vars = [];
}

let master_ctx_from_consts consts : master_ctx =
{
  lib = [];
  consts = consts;
  stack = [];
  mem = [];
  vars = [];
}

let master_ctx_from_lib lib : master_ctx =
{
  lib = lib;
  consts = [];
  stack = [];
  mem = [];
  vars = [];
}

let master_ctx_from_consts_and_lib consts lib : master_ctx =
{
  lib = lib;
  consts = consts;
  stack = [];
  mem = [];
  vars = [];
}

let master_ctx_from_vars_and_lib vars lib : master_ctx =
{
  lib = lib;
  consts = [];
  stack = [];
  mem = [];
  vars = vars;
}

let downgrade_to_typing (ctx : master_ctx) : typing_ctx =
{
  stack = List.map (fun (s, t, _) -> (s, t)) ctx.stack;
  consts = ctx.consts;
  lib = ctx.lib;
  mem = List.map snd ctx.mem;
  vars = ctx.vars;
}

let push_variable_to_master_context_stack ctx v =
  {
    stack = ctx.stack @ [v];
    consts = ctx.consts;
    lib = ctx.lib;
    mem = ctx.mem;
    vars = ctx.vars;
  }

let pop_variables_off_master_context_stack ctx n =
  {
    stack = list_pop ctx.stack n;
    consts = ctx.consts;
    lib = ctx.lib;
    mem = ctx.mem;
    vars = ctx.vars;
  }

let add_var_to_master_context ctx v =
  {
    stack = ctx.stack;
    consts = ctx.consts;
    lib = ctx.lib;
    mem = ctx.mem;
    vars = ctx.vars @ [v];
  }

let is_const c =
  match c with
  | Const _ -> true
  | _ -> false

let unwrap_const c =
  match c with
  | Const c -> c
  | _ -> failwith "unwrap error"

let bool_to_formal_bool x = Const (if x then BoolTrue else BoolFalse)

let change_cell_known ctx i e =
  let (_, t) = List.nth ctx.mem i in
  {
    stack = ctx.stack;
    consts = ctx.consts;
    lib = ctx.lib;
    mem = set_list_elem ctx.mem i (e, t);
    vars = ctx.vars;
  }

let change_cell_stack ctx i e =
  let (s, t, _) = List.nth ctx.stack (List.length ctx.stack - i - 1) in
  {
    stack = set_list_elem ctx.stack i (s, t, e);
    consts = ctx.consts;
    lib = ctx.lib;
    mem = ctx.mem;
    vars = ctx.vars;
  }

let build_call body signs arg_vals =
  Block (
    List.fold_left
    (
      fun lets ((name, _), v) ->
      lets @ [Let (name, v)]
    ) [] (List.combine signs arg_vals)
    @ [Expr body]
  , 0)

(*
let rec red_check_expr n e =
  if n < 0 then false
  else (
    match e with
    | Const _ | ConstRef _ -> true
    | And (l, r) | Or (l, r) | Equal (l, r) | Add (l, r) | Sub (l, r)
    | Multiply (l, r) | Divide (l, r) | Less (l, r) | Greater (l, r)
    | LessEqual (l, r) | GreaterEqual (l, r) | Write (l, r)
      -> red_check_expr n l && red_check_expr n r
    | Not x -> red_check_expr n x
    | Call (callee, args) -> red_check_expr n callee && List.for_all (red_check_expr n) args
    | Block (b, m) ->
      if n = 0 then (
        if m = 0 then red_check_block 0 b
        else false
      ) else red_check_block (n - m) b
  )
and red_check_block n b =
  if n < 0 then false
  else (
    match b with
    | [] -> true
    | h :: t -> (
      match h with
      | Expr e -> red_check_expr n e && red_check_block n t
      | Let (_, e) -> red_check_expr n e && red_check_block 0 t
    )
  )
*)

let rec reduction_step_expr ctx e =
  match e with
  | Const c -> (ctx, Const c)
  | ConstRef i -> (ctx, List.nth ctx.consts i |> fun (_, _, c) -> Const c)
  | And (Const BoolTrue, Const BoolTrue) -> (ctx, Const BoolTrue)
  | And (Const BoolTrue, Const BoolFalse) | And (Const BoolFalse, Const BoolTrue) | And (Const BoolFalse, Const BoolFalse) -> (ctx, Const BoolFalse)
  | And (l, r) -> (
    match (is_const l, is_const r) with
    | (false, _) -> (
      let (new_ctx, new_l) = reduction_step_expr ctx l in
      (new_ctx, And (new_l, r))
    )
    | (true, false) -> (
      let (new_ctx, new_r) = reduction_step_expr ctx r in
      (new_ctx, And (l, new_r))
    )
    | _ -> (ctx, And (l, r))
  )
  | Or (Const BoolFalse, Const BoolFalse) -> (ctx, Const BoolFalse)
  | Or (Const BoolTrue, Const BoolTrue) | Or (Const BoolTrue, Const BoolFalse) | Or (Const BoolFalse, Const BoolTrue) -> (ctx, Const BoolTrue)
  | Or (l, r) -> (
    match (is_const l, is_const r) with
    | (false, _) -> (
      let (new_ctx, new_l) = reduction_step_expr ctx l in
      (new_ctx, Or (new_l, r))
    )
    | (true, false) -> (
      let (new_ctx, new_r) = reduction_step_expr ctx r in
      (new_ctx, Or (l, new_r))
    )
    | _ -> (ctx, Or (l, r))
  )
  | Not (Const BoolFalse) -> (ctx, Const BoolTrue)
  | Not (Const BoolTrue) -> (ctx, Const BoolFalse)
  | Not x ->
    if is_const x then (ctx, Not x)
    else (
      let (new_ctx, new_x) = reduction_step_expr ctx x in
      (new_ctx, Not new_x)
    )
  | Call (Const (Rec (bodies, picked)), args) when List.for_all is_const args -> (
    let picked = List.nth bodies picked in
    let rec_vals = List.mapi (fun i _ -> Const (Rec (bodies, i))) bodies in
    (ctx, Call (Const (FnPtr picked), rec_vals @ args))
  )
  | Call (Const (FnPtr x), args) when List.for_all is_const args -> (
    let f = List.nth ctx.lib x in
    (ctx, build_call (Block f.body) f.args args)
  )
  | Call (callee, args) ->
    if is_const callee then (
      let (new_ctx, new_args) = reduce_first_on_the_list ctx args in
      (new_ctx, Call (callee, new_args))
    ) else (
      let (new_ctx, new_callee) = reduction_step_expr ctx callee in
      (new_ctx, Call (new_callee, args))
    )
  | Block (b, n) -> reduction_step_block ctx b n
  | Equal (l, r) -> (
    match (is_const l, is_const r) with
    | (false, _) -> (
      let (new_ctx, new_l) = reduction_step_expr ctx l in
      (new_ctx, Equal (new_l, r))
    )
    | (true, false) -> (
      let (new_ctx, new_r) = reduction_step_expr ctx r in
      (new_ctx, Equal (l, new_r))
    )
    | (true, true) -> (
      match (l, r) with
      | (Const (FnPtr l), Const (FnPtr r)) -> (ctx, bool_to_formal_bool (l = r))
      | (Const (NumConst l), Const (NumConst r)) -> (ctx, bool_to_formal_bool (l = r))
      | (Const BoolTrue, Const BoolTrue) | (Const BoolFalse, Const BoolFalse) -> (ctx, Const BoolTrue)
      | (Const BoolTrue, Const BoolFalse) | (Const BoolFalse, Const BoolTrue) -> (ctx, Const BoolFalse)
      | (Const (Ref l), Const (Ref r)) -> (
        match (l, r) with
        | (Known _, Stack _) -> (ctx, Const BoolFalse)
        | (Stack _, Known _) -> (ctx, Const BoolFalse)
        | (Known l, Known r) -> (ctx, bool_to_formal_bool (l = r))
        | (Stack l, Stack r) -> (ctx, bool_to_formal_bool (l = r))
      )
      | _ -> (ctx, Equal (l, r))
    )
  )
  | Write (target, e) -> (
    match (is_const target, is_const e) with
    | (_, false) -> (
      let (new_ctx, new_e) = reduction_step_expr ctx e in
      (new_ctx, Write (target, new_e))
    )
    | (false, true) -> (
      let (new_ctx, new_target) = reduction_step_expr ctx target in
      (new_ctx, Write (new_target, e))
    )
    | (true, true) -> (
      match target with
      | Const (Ref (Known i)) -> (change_cell_known ctx i (unwrap_const e), Const Nil)
      | Const (Ref (Stack i)) -> (change_cell_stack ctx i (unwrap_const e), Const Nil)
      | _ -> (ctx, Write (target, e))
    )
  )
  | MoveStackVar i -> (ctx, List.nth ctx.stack (List.length ctx.stack - i - 1) |> fun (_, _, c) -> Const c)
  | Add (Const (NumConst l), Const (NumConst r)) -> (ctx, Const (NumConst (l + r)))
  | Add (l, r) -> (
    match (is_const l, is_const r) with
    | (false, _) -> (
      let (new_ctx, new_l) = reduction_step_expr ctx l in
      (new_ctx, Add (new_l, r))
    )
    | (true, false) -> (
      let (new_ctx, new_r) = reduction_step_expr ctx r in
      (new_ctx, Add (l, new_r))
    )
    | (true, true) -> (ctx, Add (l, r))
  )
  | Sub (Const (NumConst l), Const (NumConst r)) -> (ctx, Const (NumConst (l - r)))
  | Sub (l, r) -> (
    match (is_const l, is_const r) with
    | (false, _) -> (
      let (new_ctx, new_l) = reduction_step_expr ctx l in
      (new_ctx, Sub (new_l, r))
    )
    | (true, false) -> (
      let (new_ctx, new_r) = reduction_step_expr ctx r in
      (new_ctx, Sub (l, new_r))
    )
    | (true, true) -> (ctx, Sub (l, r))
  )
  | Divide (Const (NumConst l), Const (NumConst r)) -> (ctx, Const (NumConst (l / r)))
  | Divide (l, r) -> (
    match (is_const l, is_const r) with
    | (false, _) -> (
      let (new_ctx, new_l) = reduction_step_expr ctx l in
      (new_ctx, Divide (new_l, r))
    )
    | (true, false) -> (
      let (new_ctx, new_r) = reduction_step_expr ctx r in
      (new_ctx, Divide (l, new_r))
    )
    | (true, true) -> (ctx, Divide (l, r))
  )
  | Multiply (Const (NumConst l), Const (NumConst r)) -> (ctx, Const (NumConst (l * r)))
  | Multiply (l, r) -> (
    match (is_const l, is_const r) with
    | (false, _) -> (
      let (new_ctx, new_l) = reduction_step_expr ctx l in
      (new_ctx, Multiply (new_l, r))
    )
    | (true, false) -> (
      let (new_ctx, new_r) = reduction_step_expr ctx r in
      (new_ctx, Multiply (l, new_r))
    )
    | (true, true) -> (ctx, Multiply (l, r))
  )
  | Negotiate (Const (NumConst x)) -> (ctx, Const (NumConst (-x)))
  | Negotiate x ->
    if is_const x then (ctx, Negotiate x)
    else (
      let (new_ctx, new_x) = reduction_step_expr ctx x in
      (new_ctx, Negotiate new_x)
    )
  | Greater (Const (NumConst l), Const (NumConst r)) -> (ctx, bool_to_formal_bool (l > r))
  | Greater (l, r) -> (
    match (is_const l, is_const r) with
    | (false, _) -> (
      let (new_ctx, new_l) = reduction_step_expr ctx l in
      (new_ctx, Greater (new_l, r))
    )
    | (true, false) -> (
      let (new_ctx, new_r) = reduction_step_expr ctx r in
      (new_ctx, Greater (l, new_r))
    )
    | (true, true) -> (ctx, Greater (l, r))
  )
  | Less (Const (NumConst l), Const (NumConst r)) -> (ctx, bool_to_formal_bool (l < r))
  | Less (l, r) -> (
    match (is_const l, is_const r) with
    | (false, _) -> (
      let (new_ctx, new_l) = reduction_step_expr ctx l in
      (new_ctx, Less (new_l, r))
    )
    | (true, false) -> (
      let (new_ctx, new_r) = reduction_step_expr ctx r in
      (new_ctx, Less (l, new_r))
    )
    | (true, true) -> (ctx, Less (l, r))
  )
  | LessEqual (Const (NumConst l), Const (NumConst r)) -> (ctx, bool_to_formal_bool (l <= r))
  | LessEqual (l, r) -> (
    match (is_const l, is_const r) with
    | (false, _) -> (
      let (new_ctx, new_l) = reduction_step_expr ctx l in
      (new_ctx, LessEqual (new_l, r))
    )
    | (true, false) -> (
      let (new_ctx, new_r) = reduction_step_expr ctx r in
      (new_ctx, LessEqual (l, new_r))
    )
    | (true, true) -> (ctx, LessEqual (l, r))
  )
  | GreaterEqual (Const (NumConst l), Const (NumConst r)) -> (ctx, bool_to_formal_bool (l >= r))
  | GreaterEqual (l, r) -> (
    match (is_const l, is_const r) with
    | (false, _) -> (
      let (new_ctx, new_l) = reduction_step_expr ctx l in
      (new_ctx, GreaterEqual (new_l, r))
    )
    | (true, false) -> (
      let (new_ctx, new_r) = reduction_step_expr ctx r in
      (new_ctx, GreaterEqual (l, new_r))
    )
    | (true, true) -> (ctx, GreaterEqual (l, r))
  )
  | IfThenElse (Const BoolTrue, on_true, _) -> (ctx, Block on_true)
  | IfThenElse (Const BoolFalse, _, on_false) -> (ctx, Block on_false)
  | IfThenElse (cond, on_true, on_false) ->
    if is_const cond then (ctx, IfThenElse (cond, on_true, on_false))
    else (
      let (new_ctx, new_cond) = reduction_step_expr ctx cond in
      (new_ctx, IfThenElse (new_cond, on_true, on_false))
    )
  | MoveOutOfRef (Const (Ref (Known x))) -> (ctx, List.nth ctx.mem x |> fun (c, _) -> Const c)
  | MoveOutOfRef (Const (Ref (Stack x))) -> (ctx, List.nth ctx.stack (List.length ctx.stack - x - 1) |> fun (_, _, c) -> Const c)
  | MoveOutOfRef x ->
    if is_const x then (ctx, MoveOutOfRef x)
    else (
      let (new_ctx, new_x) = reduction_step_expr ctx x in
      (new_ctx, MoveOutOfRef new_x)
    )
and reduction_step_block ctx b n =
  match b with
  | [] -> (pop_variables_off_master_context_stack ctx n, Const Nil)
  | Expr e :: [] ->
    if is_const e then (pop_variables_off_master_context_stack ctx n, e)
    else (
      let (new_ctx, new_e) = reduction_step_expr ctx e in
      (new_ctx, Block ([Expr new_e], n))
    )
  | Let (s, e) :: t ->
    if is_const e then (
      let typ = infer_type_expr (downgrade_to_typing ctx) e in
      (push_variable_to_master_context_stack ctx (s, typ, unwrap_const e), Block (Expr (Const Nil) :: t, n + 1))
    )
    else (
      let (new_ctx, new_e) = reduction_step_expr ctx e in
      (new_ctx, Block (Let (s, new_e) :: t, n))
    )
  | Expr e :: t ->
    if is_const e then (ctx, Block (t, n))
    else (
      let (new_ctx, new_e) = reduction_step_expr ctx e in
      (new_ctx, Block (Expr new_e :: t, n))
    )
and reduce_first_on_the_list ctx args =
  match args with
  | [] -> (ctx, [])
  | h :: t ->
    if is_const h then (
      let (new_ctx, new_t) = reduce_first_on_the_list ctx t in
      (new_ctx, h :: new_t)
    ) else (
      let (new_ctx, new_h) = reduction_step_expr ctx h in
      (new_ctx, new_h :: t)
    )

let rec multistep_reduction_expr ctx e n =
  if n <= 0 then (ctx, e)
  else (
    let (new_ctx, new_e) = reduction_step_expr ctx e in
    multistep_reduction_expr new_ctx new_e (n - 1)
  )
