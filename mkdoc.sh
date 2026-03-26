set -eux
DOCDIR=${DOCDIR:-./html}
mkdir -p $DOCDIR
DEPENDS=depend.d
coqdep -R _build/default/theories Wasm _build/default/theories/*.v > $DEPENDS
rocqnavi _build/default/theories/*.v _build/default/theories/*.glob \
  -title "Wasm formalisation in Rocq" \
  -d $DOCDIR -Q _build/default/theories Wasm \
  -coqlib https://rocq-prover.org/doc/V8.20.1/stdlib/ \
  -file-graph-from-depend $DEPENDS
