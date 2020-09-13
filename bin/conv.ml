(*
 This module is responsible for compiling the Rust ast into the
 representation from `formalism` module.

 Note how recursive functions are handled
*)

module SM = Map.Make(String)
module SS = Set.Make(String)

module RustUnname = struct

  (* Extracts all function definitions from items *)
  let extract_functions_from_items items = 
    items
    |>
    List.filter 
    (fun x -> 
      match x with 
      | RustTerm.FnDef _ -> true
      | _ -> false
    )
    |>
    List.map
    (fun x ->
      match x with
      | RustTerm.FnDef x -> x
      | _ -> failwith "Unreachable"
    )

  (* 
    We have our own type record to store functions here to indicate 
    that this is a function in the process of being converted into the 
    formal repr 
  *)
  type func =
  {
    args : (string * RustTerm.typ) list;
    ret_type : RustTerm.typ;
    body : RustTerm.block;
  }

  (* Builds a function lookup table form the list of function defs *)
  let convert_function_list_to_table funcs =
    List.fold_left 
    (
      fun acc f ->
      if Hashtbl.mem acc f.RustTerm.name then failwith "detected duplicate definitions"
      else (
        (* 
          Note that under the hood we treat functions which in Rust "take no arguments" 
          as functions which take a unit with "unused" name
        *)
        if f.RustTerm.args = [] then 
          Hashtbl.add acc f.RustTerm.name 
          { args = [("_unused", RustTerm.Unit)]; ret_type = f.RustTerm.ret_type; body = f.RustTerm.body }
        else 
          Hashtbl.add acc f.RustTerm.name 
          { args = f.RustTerm.args; ret_type = f.RustTerm.ret_type; body = f.RustTerm.body }
        ; 
        acc
      )
    ) (Hashtbl.create (List.length funcs)) funcs

  (* 
   return the name of all variables which are used 
   in an expression
  *)
  let rec expr_whats_used e =
    match e with
    | RustTerm.Nil -> SS.empty
    | RustTerm.Variable x -> SS.singleton x
    | RustTerm.NumConst _ -> SS.empty
    | RustTerm.Call (x, y) -> SS.union (expr_whats_used x) (y |> List.map expr_whats_used |> List.fold_left SS.union SS.empty)
    | RustTerm.Add (x, y) | RustTerm.Sub (x, y) | RustTerm.Multiply (x, y) 
    | RustTerm.Divide (x, y) | RustTerm.Less (x, y) | RustTerm.Greater (x, y) | RustTerm.LessEqual (x, y) 
    | RustTerm.GreaterEqual (x, y) | RustTerm.Equal (x, y) -> SS.union (expr_whats_used x) (expr_whats_used y)
    | RustTerm.Negotiate x -> expr_whats_used x
    | RustTerm.IfThenElse (x, y, z) -> SS.union (SS.union (expr_whats_used x) (block_whats_used y)) (block_whats_used z)
    | RustTerm.IfThen (x, y) -> SS.union (expr_whats_used x) (block_whats_used y)
    | RustTerm.Block x -> block_whats_used x
  and block_whats_used b =
    b |>
    List.fold_left 
  (
    fun (gathered, bound_names) x ->
    match x with
    | RustTerm.Let (name, e) -> (SS.union gathered (expr_whats_used e), SS.add name bound_names)
    | RustTerm.Expr e -> (SS.union gathered (expr_whats_used e), bound_names)
  )
  (SS.empty, SS.empty) |> 
  fun (x, y) -> SS.diff x y

  (*
    return the names of all variables which are not args
    and are used in fn's body
  *)
  let fn_def_whats_used args body = SS.diff (block_whats_used body) (args |> List.map fst |> SS.of_list)

  (*
    create the reference hierarchy graph
  *)
  let reference_hierarchy file =
    file |> 
    extract_functions_from_items |>
    List.map (
      fun f ->
      (f.RustTerm.name, fn_def_whats_used f.RustTerm.args f.RustTerm.body |> SS.elements)
    ) |>
    List.fold_left (fun acc (name, names) -> (Hashtbl.replace acc name names; acc)) (Hashtbl.create 255)

  (*
    Since Rust's definitions can go in any order and there's
    no syntax to indicate that some functions are mutually recursive
    or just recursive, we apply Tarjan's algorithm to figure out
    in which order the functions should actually be and which of them
    form a "mutual recursion group"
  *)
  let tarjan input =
    let inp_length = Hashtbl.length input in
    let v_index = Hashtbl.create inp_length
    and v_lowlink = Hashtbl.create inp_length 
    and v_on_stack = Hashtbl.create inp_length
    and stack = Stack.create ()
    and sccs = ref []
    and index = ref 0 in
    let rec strong_connect v = 
      Hashtbl.replace v_index v !index;
      Hashtbl.replace v_lowlink v !index;
      index := !index + 1;
      Stack.push v stack;
      Hashtbl.replace v_on_stack v ();
      List.iter 
      (
        fun w ->
        if not (Hashtbl.mem v_index w) then (
          strong_connect w;
          Hashtbl.replace v_lowlink v (min (Hashtbl.find v_lowlink v) (Hashtbl.find v_lowlink w));
        ) else if Hashtbl.mem v_on_stack w then (
          Hashtbl.replace v_lowlink v (min (Hashtbl.find v_lowlink v) (Hashtbl.find v_index w))
        )
      ) (Hashtbl.find input v);
      if (Hashtbl.find v_lowlink v) = (Hashtbl.find v_index v) then (
        let scc = ref [] in
        let w = ref (Stack.pop stack) in
        Hashtbl.remove v_on_stack !w;
        scc := !w :: !scc;
        while !w <> v do
          w := Stack.pop stack;
          Hashtbl.remove v_on_stack !w;
          scc := !w :: !scc;
        done;
        sccs := !scc :: !sccs
      )
    in
    Hashtbl.iter
    (
      fun v _ ->
      if not (Hashtbl.mem v_index v) then (strong_connect v)
    ) input;
    List.rev !sccs

  (* 
    This context assits us in tracking how variables will be laid 
    on stack and how functions will be laid out in memory 
  *)
  type translate_ctx =
  {
    next_free_address : int;
    adresses : int SM.t;
    next_free_lib_id : int;
    library : int SM.t;
    next_free_var_id : int;
    vars : int SM.t;
  }    

  let add_variable ctx name =
    {
      next_free_address = ctx.next_free_address + 1;
      adresses = SM.add name ctx.next_free_address ctx.adresses;
      next_free_lib_id = ctx.next_free_lib_id;
      library = ctx.library;
      next_free_var_id = ctx.next_free_var_id;
      vars = ctx.vars;
    }
 
  let add_func_to_lib ctx name =
    if SM.mem name ctx.library then failwith "detected a duplicate";
    {
      next_free_address = ctx.next_free_address;
      adresses  = ctx.adresses;
      next_free_lib_id = ctx.next_free_lib_id + 1;
      library = SM.add name ctx.next_free_lib_id ctx.library;
      next_free_var_id = ctx.next_free_var_id;
      vars = ctx.vars;
    }

  let add_formal_var ctx name =
    {
      next_free_address = ctx.next_free_address;
      adresses = ctx.adresses;
      next_free_lib_id = ctx.next_free_lib_id;
      library = ctx.library;
      next_free_var_id = ctx.next_free_var_id + 1;
      vars = SM.add name ctx.next_free_var_id ctx.vars;
    }

  let empty_ctx = 
    {
      next_free_address = 0;
      adresses = SM.empty;
      next_free_lib_id = 0;
      library = SM.empty;
      next_free_var_id = 0;
      vars = SM.empty;
    }

  let ctx_from_formal (ctx : RustDeBrujin.typing_ctx) : translate_ctx = 
    empty_ctx |>
    (
      fun conv_ctx ->
      List.fold_left (fun acc x -> add_func_to_lib acc x.RustDeBrujin.name) conv_ctx ctx.lib
    ) |>
    (
      fun conv_ctx ->
      List.fold_left (fun acc x -> add_formal_var acc (fst x)) conv_ctx ctx.vars
    )

  let variable_address ctx v = (SM.cardinal ctx.adresses) - (SM.find v ctx.adresses) - 1

  let function_address ctx v = SM.find v ctx.library

  let var_id ctx v = SM.find v ctx.vars

  (* Compiles the ast of the expression into an expr from `formalism.ml` *)
  let rec compile_expr ctx e =
    match e with
    | RustTerm.Nil -> RustDeBrujin.Const RustDeBrujin.Nil
    | RustTerm.Variable n -> (
      if SM.mem n ctx.adresses then RustDeBrujin.MoveStackVar (variable_address ctx n)
      else if SM.mem n ctx.library then RustDeBrujin.Const (RustDeBrujin.FnPtr (function_address ctx n))
      else if SM.mem n ctx.vars then RustDeBrujin.Const (RustDeBrujin.Var (var_id ctx n))
      else failwith (Printf.sprintf "Unbound name %s" n)
    )
    | RustTerm.NumConst c -> RustDeBrujin.Const (RustDeBrujin.NumConst c)
    | RustTerm.Call (callee, args) -> 
      (*
        Calls which in Rust give "nothing" to the functions are treated
        as calls which give function a "unit"
      *)
      if args = [] then RustDeBrujin.Call (compile_expr ctx callee, [RustDeBrujin.Const RustDeBrujin.Nil])
      else RustDeBrujin.Call (compile_expr ctx callee, List.map (compile_expr ctx) args)
    | RustTerm.Add (l, r) -> RustDeBrujin.Add (compile_expr ctx l, compile_expr ctx r)
    | RustTerm.Sub (l, r) -> RustDeBrujin.Sub (compile_expr ctx l, compile_expr ctx r)
    | RustTerm.Multiply (l, r) -> RustDeBrujin.Multiply (compile_expr ctx l, compile_expr ctx r)
    | RustTerm.Divide (l, r) -> RustDeBrujin.Divide (compile_expr ctx l, compile_expr ctx r)
    | RustTerm.Less (l, r) -> RustDeBrujin.Less (compile_expr ctx l, compile_expr ctx r)
    | RustTerm.Greater (l, r) -> RustDeBrujin.Greater (compile_expr ctx l, compile_expr ctx r)
    | RustTerm.LessEqual (l, r) -> RustDeBrujin.LessEqual (compile_expr ctx l, compile_expr ctx r)
    | RustTerm.GreaterEqual (l, r) -> RustDeBrujin.GreaterEqual (compile_expr ctx l, compile_expr ctx r)
    | RustTerm.Equal (l, r) -> RustDeBrujin.Equal (compile_expr ctx l, compile_expr ctx r)
    | RustTerm.Negotiate x -> RustDeBrujin.Negotiate (compile_expr ctx x)
    | RustTerm.IfThenElse (cond, on_true, on_false) -> RustDeBrujin.IfThenElse (compile_expr ctx cond, compile_block ctx on_true, compile_block ctx on_false)
    | RustTerm.IfThen (cond, on_true) -> 
      RustDeBrujin.IfThenElse (
        compile_expr ctx cond, compile_block ctx on_true, 
        ([RustDeBrujin.Expr (RustDeBrujin.Const RustDeBrujin.Nil)], 0)
      )
    | RustTerm.Block b -> (
      let (b, n) = compile_block ctx b in
      RustDeBrujin.Block (b, n)
    )
  (* Compiles the block into its `formalism.ml` counterpart *)
  and compile_block ctx b =
    List.fold_left
    (
      fun (ctx, b) x ->
      match x with
      | RustTerm.Let (name, e) -> (add_variable ctx name, RustDeBrujin.Let (name, compile_expr ctx e) :: b) 
      | RustTerm.Expr e -> (ctx, RustDeBrujin.Expr (compile_expr ctx e) :: b)
    ) (ctx, []) b |> 
    snd |> fun l -> (List.rev l, 0) (* The statements end up being in reverse, so we need to reverse the list *)

  (* Takes a group of functions and compiles it into a set of block from `formalism.ml` *)
  let compile_func_group inp ctx =
    (* Each function is compiled under its own unique context *)
    let new_ctxs =
      List.map (
        fun (_, f) ->
        ctx |>
        (fun ctx -> List.map fst inp |> List.fold_left add_variable ctx) |> (* Each function is aware of other functions in the group *)
        (fun ctx -> List.map fst f.args |> List.fold_left add_variable ctx) (* Each function is aware of its arguments *)
      ) inp
    in
    inp |>
    List.map snd |>
    List.combine new_ctxs |>
    List.map (
      fun (ctx, f) -> 
      let (b, n) = compile_block ctx f.body in
      (b, n)
    )

  (* A wrapper which compiles a group of functions which uses recursion *)
  let compile_recursive_set func_info_table group ctx acc =
    (* TRust creates function's "hidden" and "revealed" definitions *)
    (* The "hidden" definition takes all arguments plus the functions it's recursive with *)
    (* Such definitions start with "body#". The hashtag ensures that definition doesn't overlap with the user's definitions *)
    let hidden_names = group |> List.map ((^) "body#")
    and compiler_input = List.map (fun x -> (x, Hashtbl.find func_info_table x)) group in
    (* Call the compiler to construct the bodies of the "hidden" definitions *)
    let formal_bodies_hidden = List.combine hidden_names (compile_func_group compiler_input ctx) in
    (* We then register both "hidden" and "revealed" names *)
    let new_ctx =
      ctx |>
      (fun ctx -> List.fold_left add_func_to_lib ctx hidden_names) |>
      (fun ctx -> List.fold_left add_func_to_lib ctx group)
    in
    (* Now fetch the indices of the "hidden" definitions in the lib *)
    let hidden_formal_bodies_indices = List.map (fun x -> function_address new_ctx ("body#" ^ x)) group in
    (* This function builds the body of the "revealed" definition *)
    (* 
     As you can see, it just groups all "hidden" definitions into a `Rec`, picks `index`'th body and calls it, so it's 
     essentially just a wrapper
    *)
    let build_revealed_formal_body f index =
      let arg_count = List.length f.args in
      (
        [RustDeBrujin.Expr (
          RustDeBrujin.Call
          (
            Const (RustDeBrujin.Rec (hidden_formal_bodies_indices, index)),
            List.mapi (fun i _ -> RustDeBrujin.MoveStackVar (arg_count - i - 1)) f.args
          )
        )],
        0
      )
    in
    List.iter (Printf.printf "%s compiled\n") (hidden_names @ group);
    (* Construct the "revealed" bodies *)
    let formal_bodies_revealed = List.mapi (fun i x -> (x, build_revealed_formal_body (Hashtbl.find func_info_table x) i)) group in
    (new_ctx, acc @ formal_bodies_hidden @ formal_bodies_revealed)

  (* This function is a special case when the function doesn't use recursion *)
  (* 
    Unlike the previous functions, no `body#[name]` is created and the result of 
    conversion is simpy shoved into the `name`  
  *)
  let compile_non_recursive_singleton func_info_table group ctx acc =
    let compiler_input = List.map (fun x -> (x, Hashtbl.find func_info_table x)) group in
    let formal_bodies = List.combine group (compile_func_group compiler_input ctx) in
    let new_ctx = List.fold_left add_func_to_lib ctx group in
    List.iter (Printf.printf "%s compiled\n") group;
    (new_ctx, acc @ formal_bodies)

  (*
    takes the list of "recursive groups" and compiles them into the list
    of formal definitions. The order is preserved.
  *)
  let compile_funcs ctx func_info_table recursive_groups is_rec_table =
    List.fold_left
    (
      fun (ctx, acc) group ->
      (
        (* A quick match chooses which compilaton function to call *)
        match group with
        | [v] when not (Hashtbl.find is_rec_table v) -> compile_non_recursive_singleton
        | _ -> compile_recursive_set
      ) func_info_table group ctx acc
    ) (ctx, []) recursive_groups |>
    snd

  (* Builds a lookup table to quickly check if a function is recursive *)
  let build_is_rec_table ref_hierarchy group_lookup =
    let output = Hashtbl.create (Hashtbl.length ref_hierarchy) in
    Hashtbl.iter 
    (
      fun k v -> 
      Hashtbl.replace output k
      ( 
        not (
          not (List.mem k v) && 
          List.length (Hashtbl.find group_lookup k) = 1
        )
      ) (* If the function doesn't call itself and its group size is 1, it's not recursive *)
    ) ref_hierarchy;
    output

  let rec compile_type t =
    match t with
    | RustTerm.Int -> RustDeBrujin.Int
    | RustTerm.Unit -> RustDeBrujin.Unit
    | RustTerm.Fn (args, ret) -> RustDeBrujin.Fn (List.map compile_type args, compile_type ret)

  let translate_args args = List.map (fun (name, typ) -> (name, compile_type typ)) args

  (*
    This function is used to build list of arguments for functions with name "body#[SOMETHING]",
    since they are not present in the original fuction table
  *)
  let build_args_for_body who func_info_table group_lookup =
    let f = Hashtbl.find func_info_table who
    and mutuals = 
      Hashtbl.find group_lookup who |> 
      List.map (
        fun x -> 
        let f = Hashtbl.find func_info_table x in
        (x, RustDeBrujin.RecGroup (f.args |> translate_args |> List.map snd, compile_type f.ret_type))
      ) 
    in
    (mutuals @ (translate_args f.args), compile_type f.ret_type)

  (*
    Compiles the file. The result can be immediately fed into
    `RustDeBrujin.load_module`.
  *)
  let compile_file ctx file : RustDeBrujin.func list =
    (* Matches strings which look like "body#[SOMETHING]" *)
    let r = Str.regexp "body#\\(.+\\)" in
    let table = file |> extract_functions_from_items |> convert_function_list_to_table in
    let ref_hierarchy = reference_hierarchy file in
    let groups = tarjan ref_hierarchy in
    (* A lookup table to get the group that a function belongs to *)
    let group_lookup = 
      List.fold_left 
      (
        fun map group ->
        List.iter (fun x -> Hashtbl.replace map x group) group;
        map 
      ) (Hashtbl.create (groups |> List.flatten |> List.length)) groups
    in
    (* A table to quickly lookup if function is recursive *)
    let is_rec_table = build_is_rec_table ref_hierarchy group_lookup in
    compile_funcs ctx table groups is_rec_table |>
    (* Final steps: constructing RustDeBrujin.func *)
    List.map
    (
      fun (name, body) -> 
      (*
        Functions with "body#" at the start of their name need special treatment.
        See `build_args_for_body`
      *)
      if Str.string_match r name 0 then (
        let who = Str.matched_group 1 name in
        let (args, ret_type) = build_args_for_body who table group_lookup in 
        {
          RustDeBrujin.name = name;
          RustDeBrujin.args = args;
          RustDeBrujin.ret_type = ret_type;
          RustDeBrujin.body = body;
        } 
      )
      (* Otherwise out work is pretty simple *)
      else (
        let { args; ret_type; _ } = Hashtbl.find table name in
        {
          RustDeBrujin.name = name;
          RustDeBrujin.args = translate_args args;
          RustDeBrujin.ret_type = compile_type ret_type;
          RustDeBrujin.body = body;
        }
      )
    )

  let fetch_comments_attached_to_funcs items =
    let map = Hashtbl.create 256 in
    List.fold_left
    (
      fun acc x ->
      match x with
      | RustTerm.Comment x -> acc @ [x]
      | RustTerm.FnDef { RustTerm.name; _ } -> (Hashtbl.add map name acc; [])
    )
    []
    items |> fun _ -> ();
    map
end

module IrUnname = struct
  type translate_ctx =
  {
    lib : int SM.t;
    next_free_lib_id : int;
    vars : int SM.t;
  } 

  let translate_ctx_from_typing_ctx (ctx : IrDeBrujin.typing_ctx) : translate_ctx =
    {
      lib = ctx.lib |> List.mapi (fun i (x, _) -> (x, i)) |> List.fold_left (fun acc (k, v) -> SM.add k v acc) SM.empty;
      next_free_lib_id = List.length ctx.lib;
      vars = ctx.vars |> List.mapi (fun i (x, _) -> (x, i)) |> List.fold_left (fun acc (k, v) -> SM.add k v acc) SM.empty;
    } 

  let add_var ctx x =
    {
      lib = ctx.lib;
      next_free_lib_id = ctx.next_free_lib_id;
      vars = ctx.vars |> SM.map (fun x -> x + 1) |> SM.add x 0;
    }

  let add_func_to_lib ctx x =
    {
      lib = SM.add x ctx.next_free_lib_id ctx.lib;
      next_free_lib_id = ctx.next_free_lib_id + 1;
      vars = ctx.vars;
    }

  let compile_ptr ctx x =
    if SM.mem x ctx.lib then SM.find x ctx.lib
    else failwith "unbound pointer"

  let rec compile_term (ctx : translate_ctx) (t : IrTerm.term) : IrDeBrujin.term =
    match t with
    | IrTerm.Var x -> (
      if SM.mem x ctx.vars then IrDeBrujin.Var (SM.find x ctx.vars) 
      else failwith "unbound name" 
    )
    | IrTerm.Abs (s, domain, body) -> IrDeBrujin.Abs (s, compile_term ctx domain, compile_term (add_var ctx s) body)
    | IrTerm.App (l, r) -> IrDeBrujin.App (compile_term ctx l, compile_term ctx r)
    | IrTerm.Total -> IrDeBrujin.Total
    | IrTerm.Divergent -> IrDeBrujin.Divergent
    | IrTerm.IntegerType -> IrDeBrujin.IntegerType
    | IrTerm.IntegerConst x -> IrDeBrujin.IntegerConst x
    | IrTerm.FunctionPointer x -> IrDeBrujin.FunctionPointer (compile_ptr ctx x)
    | IrTerm.Proposition -> IrDeBrujin.Proposition
    | IrTerm.Type -> IrDeBrujin.Type
    | IrTerm.PreType -> IrDeBrujin.PreType
    | IrTerm.Predicate -> IrDeBrujin.Predicate
    | IrTerm.Kind x -> IrDeBrujin.Kind x
    | IrTerm.ComputationKind -> IrDeBrujin.ComputationKind
    | IrTerm.ComputationType (eff, typ) -> IrDeBrujin.ComputationType (compile_term ctx eff, compile_term ctx typ)
    | IrTerm.Opposite x -> IrDeBrujin.Opposite (compile_term ctx x)
    | IrTerm.Add (l, r) -> IrDeBrujin.Add (compile_term ctx l, compile_term ctx r)
    | IrTerm.Subtract (l, r) -> IrDeBrujin.Subtract (compile_term ctx l, compile_term ctx r)
    | IrTerm.Multiply (l, r) -> IrDeBrujin.Multiply (compile_term ctx l, compile_term ctx r)
    | IrTerm.Recursion (ptrs, chosen) -> IrDeBrujin.Recursion (List.map (compile_ptr ctx) ptrs, chosen)
    | IrTerm.Product (s, domain, range) -> IrDeBrujin.Product (s, compile_term ctx domain, compile_term (add_var ctx s) range)
    | IrTerm.Sequence (head, tail) -> IrDeBrujin.Sequence (compile_term ctx head, compile_term ctx tail)
    | IrTerm.AndIntroduction (l, r) -> IrDeBrujin.AndIntroduction (compile_term ctx l, compile_term ctx r)
    | IrTerm.OrIntroductionL (l_proof, r_prop) -> IrDeBrujin.OrIntroductionL (compile_term ctx l_proof, compile_term ctx r_prop)
    | IrTerm.OrIntroductionR (r_proof, l_prop) -> IrDeBrujin.OrIntroductionR (compile_term ctx r_proof, compile_term ctx l_prop)
    | IrTerm.OrElimination (on_left, on_right, proof) -> IrDeBrujin.OrElimination (compile_term ctx on_left, compile_term ctx on_right, compile_term ctx proof)
    | IrTerm.AndEliminationL (proj, proof) -> IrDeBrujin.AndEliminationL (compile_term ctx proj, compile_term ctx proof) 
    | IrTerm.AndEliminationR (proj, proof) -> IrDeBrujin.AndEliminationR (compile_term ctx proj, compile_term ctx proof)
    | IrTerm.And (l, r) -> IrDeBrujin.And (compile_term ctx l, compile_term ctx r)
    | IrTerm.Or (l, r) -> IrDeBrujin.Or (compile_term ctx l, compile_term ctx r)
    | IrTerm.MaxEffect (l, r) -> IrDeBrujin.MaxEffect (compile_term ctx l, compile_term ctx r)
    | IrTerm.DerefFnPtr x -> IrDeBrujin.DerefFnPtr (compile_term ctx x)
    | IrTerm.FnPtrType x -> IrDeBrujin.FnPtrType (compile_term ctx x)
    | IrTerm.Eq (l, r, typ) -> IrDeBrujin.Eq (compile_term ctx l, compile_term ctx r, compile_term ctx typ)
    | IrTerm.EqIntro (value, typ) -> IrDeBrujin.EqIntro (compile_term ctx value, compile_term ctx typ)
    | IrTerm.Truth -> IrDeBrujin.Truth
    | IrTerm.ProofOfTruth -> IrDeBrujin.ProofOfTruth
    | IrTerm.Falsity -> IrDeBrujin.Falsity
    | IrTerm.EqElim (pred, proof, eq_proof) -> IrDeBrujin.EqElim (compile_term ctx pred, compile_term ctx proof, compile_term ctx eq_proof)
    | IrTerm.FalsityEliminationProposition (prop, proof) -> IrDeBrujin.FalsityEliminationProposition (compile_term ctx prop, compile_term ctx proof)
    | IrTerm.FalsityEliminationType (typ, proof) -> IrDeBrujin.FalsityEliminationType (compile_term ctx typ, compile_term ctx proof)
end

module IrName = struct
  type translate_ctx = 
  {
    lib : string list;
    vars : string list;  
  }

  let translate_ctx_from_typing_ctx (ctx : IrDeBrujin.typing_ctx) : translate_ctx =
    {
      lib = ctx.lib |> List.map (fun (x, _) -> x);
      vars = ctx.vars |> List.map (fun (x, _) -> x);
    } 

  let add_var ctx x =
    {
      lib = ctx.lib;
      vars = x :: ctx.vars;
    }

  let add_func_to_lib ctx x =
    {
      lib = x :: ctx.lib;
      vars = ctx.vars;
    }

  let compile_ptr ctx x = List.nth ctx.lib x

  let rec compile_term (ctx : translate_ctx) (t : IrDeBrujin.term) : IrTerm.term =
    match t with
    | IrDeBrujin.Var x -> (
      if List.length ctx.vars <= x then failwith "Variable ID out of range"
      else IrTerm.Var (List.nth ctx.vars x) 
    )
    | IrDeBrujin.Abs (s, domain, body) -> IrTerm.Abs (s, compile_term ctx domain, compile_term (add_var ctx s) body)
    | IrDeBrujin.App (l, r) -> IrTerm.App (compile_term ctx l, compile_term ctx r)
    | IrDeBrujin.Total -> IrTerm.Total
    | IrDeBrujin.Divergent -> IrTerm.Divergent
    | IrDeBrujin.IntegerType -> IrTerm.IntegerType
    | IrDeBrujin.IntegerConst x -> IrTerm.IntegerConst x
    | IrDeBrujin.FunctionPointer x -> IrTerm.FunctionPointer (compile_ptr ctx x)
    | IrDeBrujin.Proposition -> IrTerm.Proposition
    | IrDeBrujin.Type -> IrTerm.Type
    | IrDeBrujin.PreType -> IrTerm.PreType
    | IrDeBrujin.Predicate -> IrTerm.Predicate
    | IrDeBrujin.Kind x -> IrTerm.Kind x
    | IrDeBrujin.ComputationKind -> IrTerm.ComputationKind
    | IrDeBrujin.ComputationType (eff, typ) -> IrTerm.ComputationType (compile_term ctx eff, compile_term ctx typ)
    | IrDeBrujin.Opposite x -> IrTerm.Opposite (compile_term ctx x)
    | IrDeBrujin.Add (l, r) -> IrTerm.Add (compile_term ctx l, compile_term ctx r)
    | IrDeBrujin.Subtract (l, r) -> IrTerm.Subtract (compile_term ctx l, compile_term ctx r)
    | IrDeBrujin.Multiply (l, r) -> IrTerm.Multiply (compile_term ctx l, compile_term ctx r)
    | IrDeBrujin.Recursion (ptrs, chosen) -> IrTerm.Recursion (List.map (compile_ptr ctx) ptrs, chosen)
    | IrDeBrujin.Product (s, domain, range) -> IrTerm.Product (s, compile_term ctx domain, compile_term (add_var ctx s) range)
    | IrDeBrujin.Sequence (head, tail) -> IrTerm.Sequence (compile_term ctx head, compile_term ctx tail)
    | IrDeBrujin.AndIntroduction (l, r) -> IrTerm.AndIntroduction (compile_term ctx l, compile_term ctx r)
    | IrDeBrujin.OrIntroductionL (l_proof, r_prop) -> IrTerm.OrIntroductionL (compile_term ctx l_proof, compile_term ctx r_prop)
    | IrDeBrujin.OrIntroductionR (r_proof, l_prop) -> IrTerm.OrIntroductionR (compile_term ctx r_proof, compile_term ctx l_prop)
    | IrDeBrujin.OrElimination (on_left, on_right, proof) -> IrTerm.OrElimination (compile_term ctx on_left, compile_term ctx on_right, compile_term ctx proof)
    | IrDeBrujin.AndEliminationL (proj, proof) -> IrTerm.AndEliminationL (compile_term ctx proj, compile_term ctx proof) 
    | IrDeBrujin.AndEliminationR (proj, proof) -> IrTerm.AndEliminationR (compile_term ctx proj, compile_term ctx proof)
    | IrDeBrujin.And (l, r) -> IrTerm.And (compile_term ctx l, compile_term ctx r)
    | IrDeBrujin.Or (l, r) -> IrTerm.Or (compile_term ctx l, compile_term ctx r)
    | IrDeBrujin.MaxEffect (l, r) -> IrTerm.MaxEffect (compile_term ctx l, compile_term ctx r)
    | IrDeBrujin.DerefFnPtr x -> IrTerm.DerefFnPtr (compile_term ctx x)
    | IrDeBrujin.FnPtrType x -> IrTerm.FnPtrType (compile_term ctx x)
    | IrDeBrujin.Eq (l, r, typ) -> IrTerm.Eq (compile_term ctx l, compile_term ctx r, compile_term ctx typ)
    | IrDeBrujin.EqIntro (value, typ) -> IrTerm.EqIntro (compile_term ctx value, compile_term ctx typ)
    | IrDeBrujin.Truth -> IrTerm.Truth
    | IrDeBrujin.ProofOfTruth -> IrTerm.ProofOfTruth
    | IrDeBrujin.Falsity -> IrTerm.Falsity
    | IrDeBrujin.EqElim (pred, proof, eq_proof) -> IrTerm.EqElim (compile_term ctx pred, compile_term ctx proof, compile_term ctx eq_proof)
    | IrDeBrujin.FalsityEliminationProposition (prop, proof) -> IrTerm.FalsityEliminationProposition (compile_term ctx prop, compile_term ctx proof)
    | IrDeBrujin.FalsityEliminationType (typ, proof) -> IrTerm.FalsityEliminationType (compile_term ctx typ, compile_term ctx proof)
end

module IrToString = struct
  type translate_ctx = IrName.translate_ctx

  let translate_ctx_from_typing_ctx = IrName.translate_ctx_from_typing_ctx

  let decorate_ptr s = "@" ^ s

  let rec string_of_named_ir_term t =
    match t with
    | IrTerm.Var x -> x
    | IrTerm.Abs (s, domain, body) -> Printf.sprintf "(\\%s : %s.%s)" s (string_of_named_ir_term domain) (string_of_named_ir_term body)
    | IrTerm.App (l, r) -> Printf.sprintf "(%s %s)" (string_of_named_ir_term l) (string_of_named_ir_term r)
    | IrTerm.Total -> "total"
    | IrTerm.Divergent -> "divergent"
    | IrTerm.IntegerType -> "int"
    | IrTerm.IntegerConst x -> string_of_int x
    | IrTerm.FunctionPointer x -> decorate_ptr x
    | IrTerm.Proposition -> "Prop" 
    | IrTerm.Type -> "Type"
    | IrTerm.PreType -> "PreType"
    | IrTerm.ComputationKind -> "CompKind"
    | IrTerm.Predicate -> "Predicate"
    | IrTerm.Kind x -> Printf.sprintf "Kind[%d]" x
    | IrTerm.ComputationType (eff, typ) -> Printf.sprintf "(%s<%s>)" (string_of_named_ir_term eff) (string_of_named_ir_term typ)
    | IrTerm.Opposite x -> Printf.sprintf "(-%s)" (string_of_named_ir_term x)
    | IrTerm.Add (l, r) -> Printf.sprintf "(%s + %s)" (string_of_named_ir_term l) (string_of_named_ir_term r)
    | IrTerm.Subtract (l, r) -> Printf.sprintf "(%s - %s)" (string_of_named_ir_term l) (string_of_named_ir_term r)
    | IrTerm.Multiply (l, r) -> Printf.sprintf "(%s * %s)" (string_of_named_ir_term l) (string_of_named_ir_term r)
    | IrTerm.Recursion (bodies, chosen) -> Printf.sprintf "rec[%s][%d]" (String.concat ", " (bodies |> List.map decorate_ptr)) chosen 
    | IrTerm.Product (s, domain, range) -> (
      if s = "_" then Printf.sprintf "(%s -> %s)" (string_of_named_ir_term domain) (string_of_named_ir_term range)
      else Printf.sprintf "(forall %s : %s.%s)" s (string_of_named_ir_term domain) (string_of_named_ir_term range)
    )
    | IrTerm.Sequence (head, tail) -> Printf.sprintf "(%s; %s)" (string_of_named_ir_term head) (string_of_named_ir_term tail)
    | IrTerm.AndIntroduction (l_proof, r_proof) -> Printf.sprintf "and_intro(%s, %s)" (string_of_named_ir_term l_proof) (string_of_named_ir_term r_proof)
    | IrTerm.OrIntroductionL (l_proof, r_prop) -> Printf.sprintf "or_intro_l(%s, %s)" (string_of_named_ir_term l_proof) (string_of_named_ir_term r_prop)
    | IrTerm.OrIntroductionR (r_proof, l_prop) -> Printf.sprintf "or_intro_r(%s, %s)" (string_of_named_ir_term r_proof) (string_of_named_ir_term l_prop)
    | IrTerm.OrElimination (on_left, on_right, prop) -> Printf.sprintf "or_elim(%s, %s, %s)" (string_of_named_ir_term on_left) (string_of_named_ir_term on_right) (string_of_named_ir_term prop)
    | IrTerm.AndEliminationL (proj, proof) -> Printf.sprintf "and_elim_l(%s, %s)" (string_of_named_ir_term proj) (string_of_named_ir_term proof)
    | IrTerm.AndEliminationR (proj, proof) -> Printf.sprintf "and_elim_r(%s, %s)" (string_of_named_ir_term proj) (string_of_named_ir_term proof)
    | IrTerm.And (l, r) -> Printf.sprintf "(%s /\\ %s)" (string_of_named_ir_term l) (string_of_named_ir_term r)
    | IrTerm.Or (l, r) -> Printf.sprintf "(%s \\/ %s)" (string_of_named_ir_term l) (string_of_named_ir_term r)
    | IrTerm.MaxEffect (l, r) -> Printf.sprintf "max_comp_kind(%s, %s)" (string_of_named_ir_term l) (string_of_named_ir_term r)
    | IrTerm.DerefFnPtr x -> Printf.sprintf "DEREF[%s]" (string_of_named_ir_term x)
    | IrTerm.FnPtrType x -> Printf.sprintf "FNPTR[%s]" (string_of_named_ir_term x)
    | IrTerm.Eq (l, r, typ) -> Printf.sprintf "(%s = %s :> %s)" (string_of_named_ir_term l) (string_of_named_ir_term r) (string_of_named_ir_term typ)
    | IrTerm.EqIntro (value, typ) -> Printf.sprintf "eq_intro(%s, %s)" (string_of_named_ir_term value) (string_of_named_ir_term typ)
    | IrTerm.Truth -> "Truth"
    | IrTerm.ProofOfTruth -> "truth"
    | IrTerm.Falsity -> "Falsity"
    | IrTerm.EqElim (pred, proof, eq_proof) -> Printf.sprintf "eq_elim(%s, %s, %s)" (string_of_named_ir_term pred) (string_of_named_ir_term proof) (string_of_named_ir_term eq_proof)
    | IrTerm.FalsityEliminationProposition (prop, proof) -> Printf.sprintf "false_elim_prop(%s, %s)" (string_of_named_ir_term prop) (string_of_named_ir_term proof)
    | IrTerm.FalsityEliminationType (typ, proof) -> Printf.sprintf "false_elim_type(%s, %s)" (string_of_named_ir_term typ) (string_of_named_ir_term proof)

  let string_of_de_brujin_ir_term ctx t = t |> IrName.compile_term ctx |> string_of_named_ir_term
end
