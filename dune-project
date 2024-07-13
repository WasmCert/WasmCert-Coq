(lang dune 3.0)
(using coq 0.2)
(using mdx 0.2)
(name coq-wasm)
(version 2.0.1)

(generate_opam_files true)
(license MIT)
(source (github WasmCert/WasmCert-Coq))

(package
  (name coq-wasm)
  (synopsis "Wasm formalisation in Coq")
  (description "Wasm formalisation in Coq, following the AFP formalisation of Conrad Watt")
  (depends
    (coq (and (>= 8.19) (< 8.20~)))
    (coq-compcert (>= 3.11))
    (coq-ext-lib (>= 0.11.8))
    (coq-mathcomp-ssreflect (< 2.0.0~))
    (coq-parseque (>= 0.2.0))
    (cmdliner (>= 1.1.0))
    (linenoise (>= 1.4.0))
    (mdx (>= 1.9.0))
  )
  (maintainers
    "Xiaojia Rao"
    "Martin Bodin"
  )
  (authors
    "Martin Bodin"
    "Philippa Gardner"
    "Jean Pichon"
    "Xiaojia Rao"
    "Conrad Watt"
  )
)

