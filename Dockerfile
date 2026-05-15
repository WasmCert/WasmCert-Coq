# Prebaked image: base Rocq image with all coq-wasm dependencies installed.
ARG BASE_IMAGE=rocq/rocq-prover:9.0
FROM ${BASE_IMAGE}

WORKDIR /home/rocq/wasmcert-deps
COPY --chown=rocq:rocq coq-wasm.opam ./

# Pin the package (no install) so opam can resolve its deps, install only the
# deps (not coq-wasm itself), and clean caches to keep the layer small.
# --with-test pulls in mdx, which is a test-only dep.
RUN opam pin add -n -k path coq-wasm . \
 && opam install --deps-only --with-test --yes coq-wasm \
 && opam unpin coq-wasm \
 && opam clean --all-switches --download-cache --logs --repo-cache

WORKDIR /home/rocq
