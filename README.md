## TRust
An experimental interactive lambda calculi for writing verifiable programs.

## Building & Running

To build the project you will need:
* OCaml version `4.13` or higher
* Dune version `3.16` or higher
* Ocamlyacc
* Ocamllex

### Building TRust

1. cd into the repository root
2. Run `dune build`

### Running TRust

1. cd into the repository root
2. Run `dune exec trust`

### Debugging

OCaml has a decent compatability with gdb. While there is `ocamldebug`, GDB
is much better as a tool overall.

To debug TRust, simply run `debug.sh`. 
