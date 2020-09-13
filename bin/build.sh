base_build() {
  ocamlyacc -v ast.mly
  ocamllex lex.mll
}

cleanup() {
  rm ast.ml
  rm ast.mli
  rm lex.ml
}

debug_build() {
	echo "debug build"
	base_build
	dune build main.bc
	ocamldebug ./../_build/default/bin/main/bc $@
	cleanup
}

release_build() {
	echo "release build"
	base_build
	dune build main.exe
	./../_build/default/bin/main.exe $@
	cleanup
}

if ! [ $# = 0 ]
then
	if [ "$1" = "--debug" ]
	then
		shift 1	
		debug_build $@
	elif [ "$1" = "--release" ]
	then
		shift 1	
		release_build $@
	else
		release_build $@
	fi
else
	release_build $@
fi
