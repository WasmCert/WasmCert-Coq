(lang dune 3.11)
(using coq 0.2)
(using mdx 0.2)
(name coq-wasm)
(version 2.1.0)

(generate_opam_files true)
(license MIT)
(source (github WasmCert/WasmCert-Coq))

(warnings (deprecated_coq_lang_lt_08 disabled))

(package
  (name coq-wasm)
  (synopsis "Wasm formalisation in Coq")
  (description "Wasm formalisation in Coq, following the AFP formalisation of Conrad Watt")
  (depends
    (coq (and (>= 8.20) (< 8.21~)))
    (coq-compcert (>= 3.14))
    (coq-ext-lib (>= 0.11.8))
    (coq-mathcomp-ssreflect (and (>= 2.4.0) (<= 2.5~)))
    (coq-parseque (>= 0.2.0))
    (cmdliner (>= 1.1.0))
    (linenoise (>= 1.4.0))
    (mdx (>= 1.9.0))
    (wasm (and (>= 2.0.1) (<= 2.0.1)))
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
