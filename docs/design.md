# Design of the formalization

How the Rocq development is organized, and why. The layout follows the
structure of the specification, pinned as the `clarity-vision/`
submodule.

## Core and standard library are separate layers

The spec defines a small core (special forms and 82 primitives) and a
standard library written in Clarity (`prelude.clar`), whose source is its
specification. The formalization mirrors this:

- `Syntax/`, `Typing/`, `Primitives/` and `Semantics/` formalize the core
  only.
- `Std/Prelude.v` is the prelude as an AST of the core language, not a set
  of Rocq functions. Its meaning comes from the core semantics, exactly as
  in the spec.
- `Std/Properties.v` proves that the prelude is well-typed and that each
  definition does what chapter 4 claims. A discrepancy is a spec finding.

## Typing operates on instances

Overloading, generics, reference kinds, rest parameters and inline
functions are resolved by instantiation (spec 2.6.2), and generic bodies
are type-checked only per instance ("template semantics"). The typing
pipeline is therefore:

1. `Typing/Subtyping.v`: the subtyping lattice and `lub`.
2. `Typing/Instantiation.v`: least instantiation, overload resolution, the
   capped fold-accumulator fixpoint.
3. `Typing/Inline.v`: call-by-name expansion of inline functions.
4. `Typing/Typing.v`: typing judgments on instances.
5. `Typing/StaticChecks.v`: contract-level rules (acyclic definition graph,
   no shadowing, read-only, responses handled).

The dynamic semantics (`Semantics/Eval.v`) also evaluates instances.

## The chain ABI is a parameter

The chain ABI (value wire format, interfaces, host functions) is a separate
document that does not exist yet. `Host/` declares only what the language
spec relies on, as abstract parameters:

- `Host/Crypto.v`: hash functions and signature schemes.
- `Host/Abi.v`: wire format, `serialized-size`, interfaces, trait
  implementation.
- `Host/Interface.v`: host operations (storage, assets, context, chain data,
  calls, events).

Results proved over these parameters hold for every chain that implements
the ABI. Assumptions on the parameters must stay minimal and be listed
here as they are added.

## Primitives: one file per spec section

`Primitives/Signatures.v` holds the typing signatures of all primitives
(chapter 3 tables). Their semantics is split by spec section (3.1–3.10) so
each file can be reviewed against one table.

## Metatheory: one file per property

| File | Property | Spec source |
|---|---|---|
| `TypeSafety.v` | Well-typed instances never get stuck | 2.7.1, P7 |
| `Termination.v` | Evaluation, instantiation and inline expansion terminate | P1, 2.4.3 |
| `Determinism.v` | Evaluation is a function of its inputs | 2.7.1, P7 |
| `ReadOnly.v` | Read-only code performs no writes | 2.7.4 |

## Parsing is formalized in Rocq

vNEXT syntax is S-expressions, so the parser is a regular Lisp parser
written directly in Rocq, with no parser generator. It has two layers:

1. **S-expression reader**: characters to nested lists of atoms. Beyond
   plain Lisp, it handles the lexical forms of spec 2.2: tuple literals
   `{ name: expr, ... }`, `0x` buffers, `u"..."` strings, principal
   literals (`'SP...`, `.name`), and the spread suffix `e...`.
2. **AST builder**: S-expressions to `Syntax/Ast.v`, checking the shape of
   each form (definitions, `match` arms, allowances).

They will live in `Syntax/Sexp.v` and `Syntax/Parser.v` once the spec's
grammar settles. `Syntax/Lexical.v` holds the lexical well-formedness
rules already stated (2.2). Writing the parser in Rocq keeps it inside the
proved part of the development: a print/parse round-trip property can be
proved, and the test oracle does not have to trust a hand-written parser.

## The semantics is executable: the test oracle

The architecture calls for "a direct evaluator of the spec's semantics,
used only as a test oracle" to differentially test and fuzz the compiler
(architecture, section 6). This development provides it.

### How it is built

- **Executable definitions.** The evaluator in `Semantics/Eval.v` is
  written as a Rocq function (a definitional interpreter). Where a
  relational, proof-oriented semantics is also given, the interpreter is
  proved to agree with it. Its termination argument follows from P1 and
  the acyclic definition graph (2.4.3), and lives in
  `Metatheory/Termination.v`.
- **Executable type checker.** Expected outcomes include compile errors,
  so `Typing/` provides decision procedures (type checking,
  instantiation, overload resolution, inline expansion, static checks)
  proved to agree with the typing rules.
- **A concrete test host.** `Host/` is instantiated with an in-memory
  host: maps for storage and balances, a configurable transaction context
  and chain data, an event log and an asset-movement log. Cryptographic
  primitives are bound to standard libraries at extraction time.
- **Extraction.** Parser, type checker and evaluator are extracted to
  OCaml, with Clarity's 128-bit integers represented as arbitrary
  precision integers (zarith) and overflow checked as the semantics
  specifies. OCaml is only the oracle's implementation language; the
  compiler under test targets WebAssembly.
- **Packaging.** The flake builds a `clarity-oracle` command. It takes a
  contract, an initial chain state and a sequence of calls, and outputs
  the outcome as JSON: a compile error class, or the results, events,
  asset movements and aborts of each call. This matches the content of
  a language vector in the spec plan.

### How it is used

- **Differential testing of the compiler.** Generated and hand-written
  contracts are run both through the compiler (Wasm on a Wasm engine with
  a test host) and through the oracle. A disagreement is a compiler bug,
  or a spec or formalization bug, adjudicated and recorded as P8
  requires.
- **Conformance vectors.** Authors write the inputs; the oracle computes
  the expected outcomes, so every expectation follows from the formal
  semantics.
- **Spec exploration.** Edge cases can be run while the spec is a draft,
  before any property about them is proved.

The oracle is never used on chain, and does not compute fuel: vectors do
not pin fuel (spec plan, conformance suite).

### Trusted base and main risk

The proofs guarantee that the extracted code computes the formal
semantics. Outside them: Rocq extraction, the OCaml compiler, the
cryptographic libraries, and the in-memory test host. The main practical
risk is a mismatch between the oracle's test host and the test host used
for compiled Wasm (initial balances, `contract-call?` dispatch, rollback).
Both sides must be fed from one shared description of the test chain
state, eventually derived from the chain ABI.

## Future direction: compiler correctness

The compiler targets WebAssembly, which has a mechanized semantics in
Rocq ([WasmCert-Coq](https://github.com/WasmCert/WasmCert-Coq)). This
opens two steps once the spec's compilation chapter (plan chapter 6)
exists:

- **Testing against a formal Wasm semantics.** WasmCert extracts to a
  conformant Wasm interpreter. Running the compiler's output on it in
  differential tests separates compiler bugs from Wasm engine bugs.
- **A `Compiler/` development.** A semantics-preservation theorem relating
  a Clarity program to its compiled module, in the style of CompCert,
  including the plan's claim that loop bounds guaranteed by source types
  survive compilation.

As of this writing, nixpkgs marks WasmCert as broken for Rocq 9.3. Its
packaging is to be revisited when this work starts.

## Not formalized

- Cost: the language defines none (P4).
- Clarity 1–6: out of scope of the spec. Their semantics is defined by the
  legacy implementation.
