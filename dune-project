(lang dune 2.4)
(using coq 0.1)
(using mdx 0.1)
(name Wasm)

(generate_opam_files true)
(license MIT)
(source (github WasmCert/WasmCert-Coq))

(package
  (name Wasm)
  (synopsis "Wasm formalisation in Coq")
  (description "Wasm formalisation in Coq, following the AFP formalisation of Conrad Watt"))

(package
  (name wasm_interpreter)
  (synopsis "Wasm interpreter extracted from the Coq formalisation"))
