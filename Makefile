EXE=src/main.exe

binary:
	dune build ${EXE}

byte:
	dune build ${EXE:.exe=.bc}

clean:
	dune clean
