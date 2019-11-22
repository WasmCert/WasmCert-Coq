.PHONY : all clean

all :
	dune build @all

clean :
	rm -rf _build
	rm theories/*.vo theories/*.glob theories/*.aux

