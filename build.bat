@echo off
ocamlc -c common.ml
ocamlc -c ir.ml
ocamlc -c preIr.ml
ocamlc -c lambdaAst.mli
ocamlc -c lambdaLex.ml
ocamlc -c lambdaAst.ml
ocamlc -c reprConversion.ml
ocamlc -c explicitTyping.ml
ocamlc common.cmo ir.cmo preIr.cmo lambdaAst.cmo lambdaLex.cmo reprConversion.cmo explicitTyping.cmo trust.ml -o trust.exe
del ir.cmo
del ir.cmi
del preIr.cmo
del preIr.cmi
del trust.cmo
del trust.cmi 
del lambdaLex.cmo
del lambdaLex.cmi
del lambdaAst.cmo
del lambdaAst.cmi  
del reprConversion.cmo
del reprConversion.cmi
del explicitTyping.cmo
del explicitTyping.cmi
del common.cmo
del common.cmi