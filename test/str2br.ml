open Termlib.Term
open Termlib.Util

let test = Dep {
  dep = Abs;
  mark = "x";
  ty = Const Prop;
  bod = Var "x"
}

let () =
  let orig = SampleTerms.samples in
  let procc = orig |> List.map (compile StringMap.empty)
                   |> List.map (decompile IntegerMap.empty)
  in
  assert (List.equal (fun x y -> x = y) orig procc)