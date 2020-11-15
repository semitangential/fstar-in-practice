all: out/ExampleExecutable

check: Example.Executable.fst
	~/opt/fstar/bin/fstar.exe --use_hints --use_hint_hashes --record_hints --cache_checked_modules Example.Executable.fst

clean:
	rm -rf codegen/
	rm -rf out/

codegen:
	mkdir codegen

out:
	mkdir out

ocaml: codegen Example.Executable.fst
	~/opt/fstar/bin/fstar.exe --use_hints --use_hint_hashes --record_hints --cache_checked_modules --odir codegen --codegen OCaml --extract 'Example.Executable' Example.Executable.fst

out/ExampleExecutable: ocaml out
	OCAMLPATH=~/opt/fstar/bin/ opam exec -- ocamlfind opt -package fstarlib -linkpkg -g codegen/Example_Executable.ml -o out/ExampleExecutable
