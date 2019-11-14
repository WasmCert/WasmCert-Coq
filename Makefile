.PHONY : all clean

all :
	dune build @all

clean :
	rm -rf _build

