.PHONY : all clean

all :
	dune build @all

clean :
	rm -rf _build || true
	rm theories/*.{vo,glob,aux} || true

