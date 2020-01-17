.PHONY : all clean

all :
	dune build @all

clean :
	rm -rf _build || true
	rm theories/*.vo || true
	rm theories/*.glob || true
	rm theories/*.aux || true

