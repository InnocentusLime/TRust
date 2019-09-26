@echo off
ocamllex lambdaLex.mll
ocamlyacc -v lambdaAst.mly