# clarity_verif

A Rocq formalization used to check the specification of Clarity vNEXT,
the next version of the [Clarity](https://docs.stacks.co/clarity)
smart-contract language. The specification lives in
[stx-labs/clarity-vision](https://github.com/stx-labs/clarity-vision),
included as the `clarity-vision/` submodule: the submodule commit is the
exact spec revision the formalization is written against.

## Layout

```
clarity-vision/        The specification (git submodule, pinned revision)
theories/              Rocq sources (logical root: ClarityVerif)
  Common/                Shared Rocq imports; language limits
  Syntax/                Lexical rules, types, values, abstract syntax
  Host/                  Abstract chain ABI: crypto, wire format, host functions
  Typing/                Subtyping, instantiation, inline expansion, typing, static checks
  Primitives/            Signatures and semantics of the 82 core primitives
  Semantics/             Execution state, allowances, evaluation
  Std/                   The standard library prelude (as Clarity AST) and its properties
  Metatheory/            Type safety, termination, determinism, read-only safety
  Conformance/           Concrete contracts with expected outcomes
docs/design.md         How the formalization is organized, and why
docs/findings.md       Issues found in the specification
flake.nix              Nix toolchain (Rocq 9.3 + Stdlib), package and checks
_RocqProject           Build configuration (file list, load paths)
Makefile               Wrapper around `rocq makefile`
```

When adding a `.v` file, also list it in `_RocqProject`.

## Spec ↔ Rocq mapping

Section numbers refer to the chapters in `clarity-vision/spec/`.

| Spec section | Rocq module |
|--------------|-------------|
| 1 Design principles (P1–P8) | `Metatheory/*` (the properties they promise) |
| 2.2 Lexical structure | `Syntax/Lexical.v` |
| 2.3.1, 2.3.3–2.3.6 Types, storable/interface types, variables, aliases, reference kinds | `Syntax/Types.v` |
| 2.3.2 Subtyping and lub | `Typing/Subtyping.v` |
| 2.4.1–2.4.2 Definitions, top-level expressions; 2.5 Expression forms | `Syntax/Ast.v`, `Typing/Typing.v` |
| 2.4.3 Acyclic definition graph; 2.4.5 Prelude names; 2.5.2 No shadowing | `Typing/StaticChecks.v` |
| 2.4.4 Contract interface | `Host/Abi.v` |
| 2.5.9 Context scoping and allowances | `Semantics/Allowances.v`, `Semantics/Eval.v` |
| 2.6.2 Instantiation and overload resolution | `Typing/Instantiation.v` |
| 2.6.3 Inline functions | `Typing/Inline.v` |
| 2.6.4 Result type inference; 2.6.5 Rest parameters | `Typing/Typing.v`, `Typing/Instantiation.v` |
| 2.7 Dynamic semantics | `Semantics/State.v`, `Semantics/Eval.v` |
| 2.7.4 Read-only enforcement | `Typing/StaticChecks.v`, `Metatheory/ReadOnly.v` |
| 2.8 Limits | `Common/Limits.v` |
| 3 Primitive signatures | `Primitives/Signatures.v` |
| 3.1–3.2 Arithmetic, comparison | `Primitives/Arith.v` |
| 3.3 Sequences | `Primitives/Sequences.v` |
| 3.4 Conversions and serialization | `Primitives/Conversions.v` |
| 3.5 Principals | `Primitives/Principals.v` |
| 3.6 Cryptography | `Primitives/Crypto.v`, `Host/Crypto.v` |
| 3.7 Storage | `Primitives/Storage.v` |
| 3.8 Assets | `Primitives/Assets.v` |
| 3.9 Context and chain data | `Primitives/Context.v` |
| 3.10 Events and control | `Primitives/Control.v` |
| 4 Standard library, `std/prelude.clar` | `Std/Prelude.v`, `Std/Properties.v` |
| Chain ABI (separate document) | `Host/*` (abstract) |

## Working with the specification

The build does not need the spec, but reading it alongside the proofs
does. Clone with the submodule:

```sh
git clone --recurse-submodules <this repo>
# or, in an existing clone:
git submodule update --init
```

The submodule URL is SSH, so access to `stx-labs/clarity-vision` is
required to fetch it.

### Moving to a newer spec revision

```sh
git -C clarity-vision fetch
git -C clarity-vision log --oneline HEAD..origin/main -- spec/   # what changed
git -C clarity-vision diff HEAD origin/main -- spec/
git -C clarity-vision checkout origin/main
```

Then update the modules affected by the diff (the mapping table above,
and the spec sections cited in each module header), check that `make`
passes, and commit the submodule bump **together with** the Rocq changes,
so every commit pairs proofs with the spec revision they are about.
`git diff --submodule=diff` shows the spec changes inside that commit.

Problems found in the spec go to `docs/findings.md` and upstream to
clarity-vision.

## Requirements

| Tool              | Version |
|-------------------|---------|
| Rocq (rocq-core)  | 9.3.0   |
| Rocq Stdlib       | 9.2.0   |
| GNU make          | any     |

Nix is the reference setup: these versions are pinned exactly in
`flake.nix` (`versions`) and in `flake.lock`. Without Nix, use opam
with the same versions.

## Building with Nix

Requires Nix with flakes enabled
(`experimental-features = nix-command flakes` in `nix.conf`).

```sh
nix build          # compile every proof in a sandbox (output in ./result)
nix flake check    # same, as a pass/fail check (use this in CI)
```

For day-to-day development, enter the dev shell, which provides `rocq`,
the Stdlib, `make` and `nixfmt`:

```sh
nix develop        # or, with direnv installed: direnv allow
make               # compile all theories
```

## Building without Nix (opam)

Install [opam](https://opam.ocaml.org/doc/Install.html), then create a
dedicated switch with the pinned versions:

```sh
opam init                                   # first time only
opam switch create clarity-verif 5.5.1      # OCaml >= 5.3 recommended
eval $(opam env --switch=clarity-verif)
opam install rocq-core.9.3.0 rocq-stdlib.9.2.0
```

Pin them so later `opam upgrade`s do not move them:

```sh
opam pin add rocq-core 9.3.0 --no-action
opam pin add rocq-stdlib 9.2.0 --no-action
```

Then, from the repository root (with the switch active):

```sh
make
```

## Make targets

| Command     | Effect                                    |
|-------------|-------------------------------------------|
| `make`      | Compile all theories                      |
| `make html` | Generate HTML documentation in `html/`    |
| `make validate` | Re-check compiled files with `rocqchk` and list the axioms used |
| `make clean`| Remove all build artifacts                |

`make` runs `rocq makefile` on `_RocqProject` to generate
`Makefile.rocq`, then builds with it. When you add a `.v` file, list it
in `_RocqProject`.

## Editor support (VS Code / VSCodium)

Interactive proof development uses
[VsRocq](https://github.com/rocq-prover/vsrocq), which has two parts
that must have the same version (2.5.0 is the first to support
Rocq 9.3):

- the editor extension `rocq-prover.vsrocq` (VS Code Marketplace or
  Open VSX);
- the language server `vsrocqtop`, built against the same Rocq as the
  project.

**With opam:** `opam install vsrocq-language-server.2.5.0` in the
`clarity-verif` switch, install the extension, and start the editor from
a shell where `eval $(opam env --switch=clarity-verif)` has been run (or
set `vsrocq.path` to the switch's `bin/vsrocqtop`).

**With Nix:** nixpkgs does not yet package a language server for
Rocq 9.3, so editor setup is left to each developer. The server must be
built against the project's pinned toolchain, which this flake exposes as
`legacyPackages.<system>.rocqPackages`. Point the extension at the
resulting binary with the `vsrocq.path` setting.

The language server reads `_RocqProject`, so the `ClarityVerif` load
path is set up automatically. It does not compile dependencies: run `make`
before opening a file, and again after changing a module that other files
import. Otherwise the editor reports `Unable to locate library ... with
prefix ClarityVerif` (no `.vo` yet) or an inconsistent-assumptions error
(stale `.vo`).

## Updating the toolchain

1. `nix flake update` to move nixpkgs.
2. Change `versions` in `flake.nix` (and `rocqPackages_9_X` for a new
   minor release).
3. Update the version table above and the opam commands.
4. Check that a VsRocq release supports the new Rocq version.
