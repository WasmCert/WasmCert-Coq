# Vendored CompCert files

The `.v` files in this directory are vendored from the CompCert project
(https://github.com/AbsInt/CompCert) and carry the original LGPL/INRIA
dual-license headers preserved at the top of each file. The full text of
the GNU Lesser General Public License v2.1, as required by §1 of that
license, is shipped alongside in `LICENSE.LGPL`.

## License election

CompCert as a whole is split between (a) parts the project explicitly
dual-licenses under LGPL v2.1+ / INRIA Non-Commercial, and (b) parts that
are governed solely by the INRIA Non-Commercial License. Per CompCert's
top-level LICENSE file, the LGPL-permitted parts include:

  * all files in the `lib/` directory
  * all files in the `common/` directory
  * the `Archi.v`, `Builtins1.v`, `CBuiltins.ml`, and
    `extractionMachdep.v` files in the `aarch64/`, `arm/`, `powerpc/`,
    `riscV/`, `x86/`, `x86_32/`, and `x86_64/` architecture directories

All files vendored here are drawn exclusively from those LGPL-permitted
parts (see the file list below). No files from CompCert's compiler core
(`cfrontend/`, `backend/`, `driver/`, etc.), which are INRIA-non-commercial
only, are included.

We use the vendored files under the LGPL v2.1+ option, which the rest of
coq-wasm (MIT) can depend on and which permits commercial use. The
vendored files themselves remain LGPL v2.1+; their per-file header
notices must be preserved on any redistribution.

## Provenance

Imported from AbsInt/CompCert at commit
`9a508b47e4e1d5a8df823cc159eb3f321efe0ad3` (master HEAD) on 2026-05-15.

## Files vendored

| Upstream path        | Vendored path        | Notes                                          |
| -------------------- | -------------------- | ---------------------------------------------- |
| `lib/Coqlib.v`       | `lib/Coqlib.v`       | verbatim                                       |
| `lib/Zbits.v`        | `lib/Zbits.v`        | verbatim                                       |
| `lib/IEEE754_extra.v`| `lib/IEEE754_extra.v`| verbatim                                       |
| `lib/Integers.v`     | `lib/Integers.v`     | verbatim                                       |
| `lib/Floats.v`       | `lib/Floats.v`       | verbatim                                       |
| `x86/Archi.v`        | `Archi.v`            | verbatim; 32-bit, little-endian (matches Wasm32) |
| `common/Memdata.v`   | `common/Memdata.v`   | modified — see the file's header for details   |

The vendored copy of `common/Memdata.v` retains only `encode_int` and
`decode_int` (the two functions actually used by coq-wasm) plus their
helpers. The original `common/AST.v`, `common/Values.v`, and
`common/Errors.v` have not been vendored, since coq-wasm makes no direct
use of them and the slimmed `Memdata.v` no longer pulls them in
transitively. The retained definitions are byte-for-byte identical to
the upstream versions; modification details are recorded at the top of
that file in compliance with LGPL-2.1 §2(a).
