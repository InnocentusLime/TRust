open Termlib.Term

let samples = [
  Dep {
    dep = Abs;
    mark = "x";
    ty = Const Prop;
    bod = Var "x"
  };
  Dep {
    dep = Prod;
    mark = "x";
    ty = Const Prop;
    bod = Var "x";
  };
  Dep {
    dep = Refine;
    mark = "x";
    ty = Const Prop;
    bod = Var "x";
  };
]