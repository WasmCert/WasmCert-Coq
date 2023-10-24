(lang dune 3.0)
(using coq 0.2)
(using mdx 0.2)
(name coq-iris-wasm)
(version da711c7-dirty)

(generate_opam_files true)
(license MIT)
(source (github WasmCert/WasmCert-Coq#iris-wasm-opam))

(package
  (name coq-iris-wasm)
  (synopsis "Wasm formalisation in Coq")
  (description "Wasm formalisation in Coq, following the AFP formalisation of Conrad Watt")
  (depends
    (coq (and (>= 8.13.2) (<= 8.13.2)))
    coq-compcert
    (coq-mathcomp-ssreflect (<= 1.17.0))
    (coq-itree (>= 3.1.0))
    (coq-iris (<= 3.6.0))
    coq-stdpp
    (coq-parseque (>= 0.1.0))
    (linenoise (>= 1.4.0))
    (mdx (>= 1.9.0))
  )
  (maintainers
    "Xiaojia Rao"
  )
  (authors
    "Xiaojia Rao"
    "Aina Linn Georges"
    "Maxime Legoupil"
    "Conrad Watt"
    "Jean Pichon-Pharabod"
    "Philippa Gardner"
    "Lars Birkedal"
  )
)

