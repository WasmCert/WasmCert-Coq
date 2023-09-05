(lang dune 2.9)
(using coq 0.1)
(using mdx 0.1)
(name Wasm)
(version 35c0a7d-dirty)

(generate_opam_files true)
(license MIT)
(source (github WasmCert/WasmCert-Coq))

(package
  (name Wasm)
  (synopsis "Wasm formalisation in Coq")
  (description "Wasm formalisation in Coq, following the AFP formalisation of Conrad Watt")
  (depends
    (coq (and (>= 8.15) (<= 8.16.1)))
    (coq-compcert (>= 3.11))
    (coq-mathcomp-ssreflect (and (>= 1.16.0) (<= 1.17.0)))
    (coq-itree (>= 3.1.0))
    (coq-parseque (>= 0.1.0))
  )
  (authors
    "Martin Bodin"
    "Philippa Gardner"
    "Jean Pichon"
    "Xiaojia Rao"
    "Conrad Watt"
  )

)

; (package
;   (name wasm_interpreter)
; 	(depends Wasm)
;   (synopsis "Wasm interpreter extracted from the Coq formalisation"))
