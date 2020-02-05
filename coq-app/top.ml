open Core
open TopParser

let prompt () = print_string "\nCoc < "; flush stdout;;

let parse_ast strm = parse_top_level_string strm;;


(*> affichage *)
let string_of_sort =
  function 
  | Kind -> "Kind"
  | Prop -> "Prop"
  | Set -> "Set"
;;

let rec string_of_expr = 
  function
  | SRT s -> string_of_sort s
  | REF x -> x
  | ABS (x,tt,t) -> "["^x^":"^(string_of_expr tt)^"]"^(string_of_expr t)
  | APP (u,v) -> "("^(string_of_app u)^" "^(string_of_expr v)^")"
  | PROD (x,tt,u) ->
      (
        match is_free_var x u with
        | true -> "("^x^":"^(string_of_expr tt)^")"^(string_of_expr u)
        | false -> (string_of_arrow tt)^"->"^(string_of_expr u)
      )
and string_of_app = 
  function
  | APP (u,v) -> (string_of_app u)^" "^(string_of_expr v)
  | t -> string_of_expr t
and string_of_arrow = 
  function
  | ABS (x0,x1,x2) -> "("^(string_of_expr (ABS (x0,x1,x2)))^")"
  | PROD (x0,x1,x2) -> "("^(string_of_expr (PROD (x0,x1,x2)))^")"
  | t -> string_of_expr t
;;

let print_expr e = print_string (string_of_expr e);;

let rec print_names = function
  | Nil -> ()
  | Cons (x, l) ->
      print_names l;
      print_string (x^" ")
;;

(*
let rec print_terms = function
  | Nil -> ()
  | Cons(t,l) ->
      print_string "x. : ";
      print_term t;
      print_newline();
      print_terms l
;;

let print_local_ctx = function
  | Nil -> print_newline()
  | l ->
      print_endline "Dans le contexte:";
      print_terms l
;;
*)

let print_message = function
  | Pnew_axiom x ->
      print_endline (x^" admitted.")
  | Pinfered_type e ->
      print_string "Inferred type: ";
      print_expr e;
      print_newline()
  | Pcorrect ->
      print_endline "Correct."
  | Pcontext_listing l ->
      print_string "Axioms: ";
      print_names l;
      print_newline()
  | Pdelete_axiom x ->
      print_endline (x^" removed.")
  | Pexiting ->
      print_endline "\nGoodbye..."; exit 0
;;

let rec print_type_err = function
  | Punder (x,e,err) ->
      print_string x;
      print_string " : ";
      print_expr e;
      print_newline();
      print_type_err err
  | Pexpected_type(m,at,et) ->
      print_string "The term ";
      print_expr m;
      print_string " has_type ";
      print_expr at;
      print_string " but it was expected to have ";
      print_expr et;
      print_endline "."
  | Pkind_ill_typed ->
      print_endline "Ill typed kind."
  | Pdb_error n ->
      print_string "The De Brujin variable #";
      print_int (int_of_nat n);
      print_endline " was not found."
  | Plambda_kind t ->
      print_string "The term ";
      print_expr t;
      print_endline " is an abstraction on a kind."
  | Pnot_a_type(m,t) ->
      print_string "The type of ";
      print_expr m;
      print_string ", which is ";
      print_expr t;
      print_endline " is not convertible to a kind."
  | Pnot_a_fun(m,t) ->
      print_string "The type of ";
      print_expr m;
      print_string ", which is ";
      print_expr t;
      print_endline " is not convertible to a prduct."
  | Papply_err(u,tu,v,tv) ->
      print_string "The term ";
      print_expr u;
      print_string " of type ";
      print_expr tu;
      print_string " cannot be applied to ";
      print_expr v;
      print_string " which has type ";
      print_expr tv;
      print_endline "."
;;

let print_type_error err =
  begin
    match err with
        Punder _ ->
          print_endline "In context:";
      | _ -> ()
  end;
  print_type_err err
;;


let print_error = 
  function
  | Punbound_vars l ->
      print_string "Unknown variables: [ ";
      print_names l;
      print_endline "]."
  | Pname_clash x ->
      print_endline ("Name "^x^" is already used.")
  | Ptype_error te ->
      print_type_error te
  | Pcannot_delete ->
      print_endline "The context is already empty."
;;



(*> encapsulation de l'etat *)
let 
update_state = 
  let state = ref empty_state in
    (fun ast -> 
       match (interp_ast !state ast) with
         | Inl(Pair(ns,msg)) ->
             print_message msg;
             state := ns
         | Inr err ->
             print_string "Error: ";
             print_error err)
;;


(*> boucle toplevel *)

let read_cmd () = 
  let succ = ref false
  and result = ref AST_QUIT in
  while not !succ do 
    try
      prompt ();
      result := parse_ast (read_line ()); 
      succ := true
    with
    | _ -> print_string "Unexpected error: Failed to read input\n"
  done;
  !result
;;

let go () =
  let cmd = ref (read_cmd ()) in
  while !cmd <> AST_QUIT do
	update_state !cmd;
    cmd := read_cmd ()
  done
;;

go();;
