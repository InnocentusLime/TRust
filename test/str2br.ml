open Termlib.Term
open Termlib.Util

let test = Dep {
  dep = Abs;
  mark = "x";
  ty = Const Prop;
  bod = Var "x"
}

let () =
  Printf.printf "%s\n" (stringify_ast test);
  Printf.printf "%s\n" (test |> compile StringMap.empty |> stringify_de_bruj);
  Printf.printf "%s\n" (test |> compile StringMap.empty |> decompile IntegerMap.empty |> stringify_ast);