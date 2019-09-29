@echo off
ocamlc -c common.ml
ocamlc -c ir.ml
ocamlc -c preIr.ml
ocamlc -c reprConversion.ml
ocamlc -c lambdaAst.mli
ocamlc -c lambdaLex.ml
ocamlc -c lambdaAst.ml
ocamlc -c typing.ml
ocamlc common.cmo ir.cmo preIr.cmo lambdaAst.cmo lambdaLex.cmo reprConversion.cmo typing.cmo rust.ml -o rust.exe
del ir.cmo
del ir.cmi
del preIr.cmo
del preIr.cmi
del rust.cmo
del rust.cmi 
del lambdaLex.cmo
del lambdaLex.cmi
del lambdaAst.cmo
del lambdaAst.cmi  
del reprConversion.cmo
del reprConversion.cmi      
del typing.cmo
del typing.cmi