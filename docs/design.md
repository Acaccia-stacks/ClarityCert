# Design of the formalization

How the Rocq development is organized, how it connects to the Rust
production compiler, and why. The layout follows the structure of the
specification, pinned as the `clarity-vision/` submodule. The rationale
for the project and its phases are in [motivation.md](motivation.md).

## Principles

- **The prose spec is normative**, together with its grammar
  (`grammar/clarity.ebnf`, chapter 5). The formal semantics is a precise
  reading of them. Where the two disagree, the disagreement is a finding
  ([findings.md](findings.md)) settled in the spec, not an automatic win
  for Rocq. This matches the spec plan: for the core language, the prose
  rule is normative.
- **Rocq is the reference, Rust is the product.** The production compiler
  is written in Rust. This development is what it is checked against, and
  stays out of the production path.
- **Everything executable is extracted from what is proved.** The parser,
  type checker and evaluator are Rocq functions proved against the rules,
  then extracted, so the tools used for testing compute exactly what the
  proofs are about.

# Part I. The Rocq development

## Core and standard library are separate layers

The spec defines a small core (special forms and 71 primitives) and a
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

Overloading, generics, reference kinds, rest parameters and macros are
resolved by instantiation (spec 2.6.2), and generic bodies
are type-checked only per instance ("template semantics"). The one
exception is the definition graph: it is over names, computed from the
source alone, and checked before any instance exists (2.4.3), which is
what makes instantiation and macro expansion finite. The typing pipeline
is therefore, on a contract the parser accepted:

1. `Typing/StaticChecks.v`, name-level part: a declared version the
   checker implements (2.4.0), reserved names never rebound (2.2), one
   namespace for top-level names, shared only by overloads (2.4),
   scoping and no shadowing (2.5.2), the acyclic definition graph (2.4.3)
   and the deploy-order check (2.4.2). Keywords are not checked here:
   the grammar excludes them from binding positions, so binding one is a
   parse error.
2. `Typing/Elaborate.v`: the source syntax resolved against the
   contract being deployed. A deployer-relative contract or trait gets
   its full name (2.2), an alias its type (2.3.6), a static constant in
   a size its value, and a name in type position is told apart as an
   alias, a type variable or a misplaced trait name (C10).
3. `Typing/Subtyping.v`: the subtyping preorder and the join. With
   equivalent traits (2.3.2), the join is a defined operation, taken over
   a whole set at once, not the order-theoretic least upper bound.
4. `Typing/Instantiation.v`: least instantiation, overload resolution for
   calls and function references, the capped fold-accumulator fixpoint;
   and, on definitions, the check that overloads do not overlap (2.6.2).
   Reference kinds are matched by kind (2.3.7): identical types for
   variables, maps and NFTs; for `(event T)`, a declared type that is a
   supertype of `T`, which fixes a variable occurring only in event
   references at the declared type.
5. `Typing/Macros.v`: expansion of macros, typed at their declared
   parameter types (2.6.3).
6. `Typing/Typing.v`: typing judgments on instances.
7. `Typing/StaticChecks.v`, instance-level part: responses handled,
   `impl-trait` conformance, read-only enforcement, the function call depth
   limit (2.7.5).

Chapter 5.4 lists the static errors most likely to be looked for in the
grammar, labelled C1–C15. The labels are only names for the grammar's
side conditions, not rule identifiers, but they map each check above to
the place where the grammar stops.

The dynamic semantics (`Semantics/Eval.v`) also evaluates instances.

## The chain ABI is a parameter

The chain ABI is specified apart from the language, in two layers, both
still proposals: a runtime layer shared by every source language
(`clarity-vision/07-chain-abi.md`) and a value interpretation layer
(`clarity-vision/08-value-interpretation.md`). `Host/` declares only what
the language spec relies on, as abstract parameters:

- `Host/Crypto.v`: hash functions and signature schemes.
- `Host/Abi.v`, the value layer: canonical encoding, `serialized-size`,
  the `abi.types` section (with the data type of each event), trait
  conformance, argument and result encoding, the storage layout.
- `Host/Interface.v`, the runtime layer: an untyped key-value store,
  assets, context and chain data, calls with their `read_only` and result
  flags, frames, events, `abort`. A contract event is emitted by its
  index in the interface's `events` list and carries the event's name and
  its data bytes; every event has a size fixed by the ABI, and the
  transaction's event bytes, which a rolled-back frame gives back, are
  capped (`events-exceeded`). `log` output is passed to the host and
  discarded: it is not an event.

The chain does not check values against declared types: a Clarity module
decodes and validates its own arguments and the results of its calls
(spec 2.5.8). The semantics therefore models that validation itself, as
runtime errors of the calling or called contract.

Once the proposals settle, the parameters with a fixed definition
(encoding, `serialized-size`, the storage layout) can be made concrete.
The direct evaluator needs them: an event's data is the canonical
encoding of the emitted value, so the events of a vector are bytes that
only a concrete encoding can produce.

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
| `Termination.v` | Evaluation, instantiation and macro expansion terminate | P1, 2.4.3 |
| `Determinism.v` | Evaluation is a function of its inputs; typing is unique | 2.7.1, P7, 2.6.2 |
| `ReadOnly.v` | Read-only code performs no writes | 2.7.4 |

## Parsing is formalized in Rocq

The syntax is defined by the spec's grammar (chapter 5,
`grammar/clarity.ebnf`) in two levels: Part L turns characters into
tokens and separators, and Part S builds forms from the tokens. The
parser follows the same split, written directly in Rocq with no parser
generator:

1. **Lexer** (`Syntax/Lexer.v`): characters to tokens. It applies the
   longest match (T1), requires a delimiter after every token other than
   punctuation (T2), admits only the characters of T3, enforces the
   layout rule W1, and makes the checks that depend on the token alone
   (LX1–LX5). The syntax is not a plain Lisp: `u2f` and `x(f)` are
   errors, not two tokens, and `...` is a token of its own.
2. **Parser** (`Syntax/Parser.v`): tokens to `Syntax/Ast.v`, by the
   Part S rules. Beyond the shape of each form (the leading
   `clarity-version`, definitions, allowances), these include the six
   `match` arm pairs, keywords excluded from binding names, the dedicated
   forms of `map` and of the six primitives that take a type or size, a
   spread only as the last argument, and the checks that depend on where
   a token occurs (LX6, LX7).

Every failure in either layer is a **parse error** (T4), a class of its
own, reported before any type checking. What the grammar accepts and the
type checker rejects (5.4) belongs to `Typing/`, so the AST must keep
such inputs representable: a size argument may be an `int` literal (C11),
and a name in type position stays unresolved until elaboration decides
whether it is an alias, a type variable or a misplaced trait name (C10).

`Syntax/Lexical.v` states the lexical rules as predicates (2.2, 5.3),
against which the lexer is proved. Writing the parser in Rocq keeps it
inside the proved part of the development, and the direct evaluator does
not have to trust a hand-written parser. Each literal has one spelling up
to digit separators, and a source is fixed up to layout and trailing
commas, so a canonical printer exists and `parse (print a) = a` can be
proved for every AST `a`.

## The direct evaluator

The architecture calls for "a direct evaluator of the spec's semantics,
used only as a test oracle" to differentially test and fuzz the compiler
(architecture, section 6). This development provides it, extracted from
the formal semantics. It is an interpreter for vNEXT: it parses a
contract, type-checks it, and evaluates calls directly on the checked
program, with no compilation and no Wasm.

### How it is built

- **Executable definitions.** The evaluator in `Semantics/Eval.v` is
  written as a Rocq function (a definitional interpreter). Where a
  relational, proof-oriented semantics is also given, the interpreter is
  proved to agree with it. Its termination argument follows from P1 and
  the acyclic definition graph (2.4.3), and lives in
  `Metatheory/Termination.v`.
- **Executable type checker.** Expected outcomes include compile errors,
  so `Typing/` provides decision procedures (type checking,
  instantiation, overload resolution, macro expansion, static checks)
  proved to agree with the typing rules.
- **A concrete test host.** `Host/` is instantiated with an in-memory
  host: maps for storage and balances, a configurable transaction context
  and chain data, an event log and an asset-movement log, and a
  configurable cap on event bytes, which the ABI leaves open. Cryptographic
  primitives are bound to standard libraries at extraction time.
- **Extraction.** Parser, type checker and evaluator are extracted to
  OCaml, with Clarity's 128-bit integers represented as arbitrary
  precision integers (zarith) and overflow checked as the semantics
  specifies. OCaml is only the direct evaluator's implementation language;
  the compiler under test targets WebAssembly.
- **Packaging.** The flake builds the direct evaluator as a
  `clarity-oracle` command. It takes a contract, an initial chain state
  and a sequence of calls, and outputs the outcome as JSON: a parse
  error, a static error class, or the results, events (contract, name and
  data), asset movements and aborts of each call. This matches the
  content of a language vector in the spec plan. `log` output is not part
  of the outcome, since the chain discards it; the command may show it
  separately for debugging.

### How it is used

- **Differential testing of the compiler.** Generated and hand-written
  contracts are run both through the compiler (Wasm on a Wasm engine with
  a test host) and through the direct evaluator. A disagreement is a
  compiler bug, or a spec or formalization bug, adjudicated and recorded
  as P8 requires.
- **Conformance vectors.** Authors write the inputs; the direct evaluator
  computes the expected outcomes, so every expectation follows from the
  formal semantics.
- **Spec exploration.** Edge cases can be run while the spec is a draft,
  before any property about them is proved.

The direct evaluator is never used on chain, and does not compute fuel:
vectors do not pin fuel (spec plan, conformance suite).

### Its own trusted base

The proofs guarantee that the extracted code computes the formal
semantics. Outside them: Rocq extraction, the OCaml compiler, the
cryptographic libraries, and the in-memory test host. The main practical
risk is a mismatch between the direct evaluator's test host and the test
host used for compiled Wasm (initial balances, `contract-call?` dispatch,
rollback). Both sides must be fed from one shared description of the test
chain state, eventually derived from the chain ABI.

## Contract verification: `Logic/`

The semantics is also what contract authors and auditors prove properties
against. A `Logic/` part, built in the last phase of the plan, makes that
practical without unfolding the semantics by hand.

- **Assertions over the execution state.** Predicates on storage (data
  variables, maps), token balances and supplies, the execution context,
  and the event and asset-movement logs.
- **A program logic.** A weakest-precondition calculus over core
  expressions, in the style of Mi-Cho-Coq for Michelson. It must handle
  the outcomes of `Semantics/Eval.v`: normal values, early `return`, and
  aborts, as well as nested state frames with rollback and the allowance
  check of `as-contract?` and `restrict-assets?`. It is proved sound with
  respect to `Semantics/Eval.v`.
- **Contract-level reasoning.** An invariant of a contract holds if it is
  established at deploy (2.4.2) and preserved by every public function.
  A public call that returns `err` is rolled back (2.7.3), so only `ok`
  outcomes need to preserve it. No reentrancy (2.7.5) means a call cannot
  observe the contract mid-update. Calls to other contracts are reasoned
  about through the callee's specification, or as arbitrary behavior
  bounded by the allowances in force.
- **Reuse of proved facts.** The properties of `Std/Properties.v` serve
  as ready-made specifications of every prelude function, and termination
  (`Metatheory/Termination.v`) turns partial-correctness results into
  total ones.
- **From source to proof.** A contract is read by the Rocq parser from its
  source text, so a proof is about that exact text, and attaches to its
  source hash in the triple the architecture ties analyses to (source
  hash, compiler version, module hash).

The spec plan lists first-class verification annotations (invariants,
pre- and postconditions) as a language design opportunity. If they are
adopted, they become goals stated in this logic.

## Conventions

Rules the Rocq sources follow throughout. Modules explain only what is
specific to them.

- **Invariants are part of the representation.** A rule that holds of
  every value of a kind (an integer's range, a character's set, a
  principal's version and hash length) is stored with the value as a
  boolean proof, `p x = true`: `refined` in `Common/Base.v`, and the
  principal records. Invalid values cannot be represented. Two proofs of
  a boolean equation are equal (`UIP_dec`), so two such values are equal
  when their data are (the `_ext` lemmas), with no axiom. A rule whose
  violation is an error to report (a repeated tuple field, C15) is a
  predicate instead, since the checker must be able to see the invalid
  input.
- **Predicates are boolean functions.** `storable`, `sorted_tuples`,
  `value_has_type` and the like return `bool`, so they compute, and
  examples are checked by `reflexivity`. A `b` suffix marks the boolean
  version of a relation that also has a `Prop` form (`ty_eqb`), with a
  lemma linking the two (`ty_eqb_eq`).
- **Decisions end with `Defined`.** A decision such as
  `ty_eq_dec : {s = t} + {s <> t}` is a function that later code branches
  on. Ending it with `Qed` would make it opaque, and an
  `if ty_eq_dec s t then … else …` would never reduce, inside examples,
  conformance vectors or proofs by computation. Ending it with `Defined`
  keeps it computable. The proof inside `left` or `right` may use opaque
  lemmas: computation only needs to reach `left` or `right`. Lemmas that
  only state facts end with `Qed`.
- **Nested inductives get their own induction principle.** For a type
  that contains itself through `list` or `prod` (tuple types, lists of
  values), the principle Rocq generates gives no induction hypothesis for
  the nested occurrences. Generation is turned off around the inductive
  (`Local Unset Elimination Schemes`), a principle over `Forall` is
  written by hand under the usual name (`ty_ind`), and it is registered
  (`Register Scheme … as ind_nodep`), so a plain `induction` uses it.
  Equality on such a type is a boolean function proved correct, since
  `decide equality` gets stuck on the nested occurrences.
- **Helpers stay local.** A definition or lemma used only to prove a
  module's own results is `#[local]`, so importers see only the public
  statement (`fields_sorted_nodup`, not `names_sorted_nodup`).
- **Examples come from the spec.** Each section ends with an `Example`
  checked by computation, built from cases the spec states (the listings
  event of 3.10, the registry of 2.3.4), so a definition is pinned to
  what the spec says and not only to the lemmas proved about it.

## Libraries

| Use | Library | Where |
|---|---|---|
| Integers, strings, lists | Rocq Stdlib | Everywhere |
| Finite maps (environments, storage), decidable equality | stdpp | `Syntax/`, `Semantics/`, `Host/` |
| Well-founded recursion and dependent pattern matching, for termination arguments | Equations | `Semantics/Eval.v`, `Typing/Instantiation.v`, `Metatheory/` |
| Monads, for an interpreter with errors and state | ExtLib | `Semantics/Eval.v`, `Typing/` |
| Extraction to OCaml, 128-bit integers as arbitrary-precision integers | Rocq extraction, zarith | The direct evaluator and the checkers |
| Formal WebAssembly semantics | WasmCert-Coq | `Compiler/` (phase 4) |
| Property-based testing inside Rocq | QuickChick | Optional |

The lexer and parser use no S-expression library: the token rules of
chapter 5 (delimiters, layout, tuple punctuation, `...`) are not those
of a generic Lisp reader such as Ceres.

All of these are packaged in nixpkgs for the pinned Rocq 9.3, except
WasmCert-Coq and QuickChick, which are marked broken there. WasmCert-Coq
supports Rocq 9.0 to 9.2 as of its v2.2.1 release, with a port to newer
Rocq versions in progress; its packaging is to be revisited when phase 4
starts. ConCert's typed extraction, which can generate a subset of Rust
from Rocq, is also broken for 9.3, so every extracted tool is an OCaml
program run as a separate process.

# Part II. Interface with the Rust compiler

## Crates and their Rocq counterparts

| Crate | Role | Rocq counterpart | Candidate libraries |
|---|---|---|---|
| `clarity-syntax` | Lexer, parser and AST | `Syntax/Lexer.v`, `Syntax/Parser.v` | Hand-written from the spec's EBNF, with the same parse errors |
| `clarity-types` | Instantiation, macro expansion, typing, static checks; exports its decisions | `Typing/` | `serde` and `serde_json` for the exported record |
| `clarity-std` | The prelude source and its tests | `Std/` | |
| `clarity-compiler` | Lowering to Wasm, prelude linking, interface and provenance sections | `Compiler/` (validator) | `wasm-encoder` to emit modules, `wasmparser` to validate them |
| `clarity-verify` | Rebuilds a module from source and runs the validator | `Compiler/` | |
| Test harness | Conformance vectors, differential tests, fuzzing | The direct evaluator | `wasmi`, the chain's engine, with an in-memory host; `proptest` and `cargo-fuzz` to generate contracts |

**Integers.** Clarity's `int` and `uint` are 128-bit, which maps directly
to Rust's `i128` and `u128` with checked arithmetic: an overflow is an
abort, as the semantics requires.

**Emitting Wasm.** `wasm-encoder` is preferred to `walrus`:

- it is maintained by the Bytecode Alliance in the `wasm-tools`
  repository, together with `wasmparser` and `wasm-smith` (random valid
  modules, for fuzzing at the Wasm level), released in step with them;
- it is a low-level encoder: the compiler decides every byte and its
  order, so the byte-identical output the architecture requires for
  reproducible builds and golden build vectors depends only on the
  compiler's own code;
- it imposes no second intermediate representation on a compiler that
  already has its own.

`walrus` offers a higher-level, editable module representation, but it
left the archived rustwasm organization in 2025 and mainly serves
`wasm-bindgen`. Hash functions are host functions in the chain ABI, so
nothing pre-built has to be merged into a module for them. The question
returns if the compiler links faster hand-written implementations of
prelude functions, which the spec allows (chapter 4.1): merging pre-built
Wasm with index renumbering must then work with `wasmparser` and
`wasm-encoder`, or those implementations must go through the compiler's
own intermediate representation.

## Level 1: testing

The compiler's continuous integration runs:

- the conformance vectors, with outcomes computed by the direct
  evaluator;
- differential tests and fuzzing: the same contracts and calls run through
  the compiled Wasm (on `wasmi`, the engine the chain ABI names, with a
  test host) and through
  `clarity-oracle`, comparing results, events, asset movements and aborts;
- the front-end comparison of level 2 on every test contract.

The direct evaluator is built by Nix and called as a separate program, so
the Rust code base does not depend on Rocq.

## Level 2: the front-end checker

`clarity-types` exports, for each contract, a record of its decisions as
JSON, keyed by source span so that both sides refer to the same
expression without sharing data structures:

- the instances it created: definition (name and overload), substitution
  of type, size and reference variables, and inferred result type;
- the instance each call resolves to;
- the inferred type of each expression;
- the order of deploy-time code;
- the `abi.interface` and `abi.types` sections emitted in the module;
- or, for a rejected contract, whether it is a parse error or a static
  error, the static error's class, and its span.

An illustrative record, for a contract calling `(unwrap-or-zero (some 5))`:

```json
{
  "result": "accepted",
  "instances": [
    { "id": 0,
      "definition": { "name": "unwrap-or-zero", "overload": 0 },
      "substitution": { "T": "(optional int)" },
      "references": {},
      "result_type": "int" }
  ],
  "calls": [ { "span": [120, 145], "instance": 0 } ],
  "types": [ { "span": [136, 144], "type": "(optional int)" } ]
}
```

The front-end checker, in `Compiler/`, runs the reference checker of
`Typing/` on the same source and compares the records for equality.
Equality is a complete check given the uniqueness of typing
(`Metatheory/Determinism.v`): if the records match, the Rust result is
the one the rules prescribe; if they differ, the first differing span
locates the disagreement. Recomputing is preferred to validating a
certificate: the full checker is built and proved anyway, and proving
that an instantiation is the least one, or that no other overload admits
a call, would redo most of its work.

Comparing rejections requires the spec to fix which error class is
reported when a contract has several errors. It does so only in part: a
parse error is reported before any type checking (5.2, T4), but nothing
orders two static errors ([findings.md](findings.md)).

## Level 3: translation validation

Given a source contract and the module `clarity-compiler` emitted, the
validator in `Compiler/` confirms that the module behaves as the source
under the Clarity and WebAssembly semantics, including the spec plan's
claim that loop bounds guaranteed by source types survive compilation. It
uses the front-end record, once checked, to match each Wasm function to
the source instance it implements. It is proved correct once; the
compiler stays untrusted.

It runs in the compiler's continuous integration and in `clarity-verify`
on deployed modules, after the front-end checker. WasmCert-Coq also
extracts to a conformant Wasm interpreter: running compiled modules on it
in differential tests separates compiler bugs from Wasm engine bugs. The
chain's Wasm profile admits bulk memory (`memory.copy`, `memory.fill`),
so the WasmCert-Coq version used must cover those operators.

## Level 4: proving Rust code

For the most critical code, the Rust source itself can be proved equal to
the Rocq definitions after translation into a proof assistant:

- **hax** (Cryspen) translates a large subset of Rust to Rocq, F* and
  Lean;
- **Aeneas** translates safe Rust to Lean, HOL4, Coq and F*, its Lean and
  HOL4 backends being the most mature;
- **rocq-of-rust** (Formal Land) translates Rust programs to Rocq.

The verified code must stay within the subset the chosen tool supports,
which constrains how it is written from the start. Candidates are the
code where an error is most damaging: the type checker's core, the
lowering of arithmetic and of asset primitives, and the allowance checks.

# Part III. The end-to-end guarantee

## What remains trusted

With levels 1 to 3 in place, a validated contract behaves as its source
says, under these assumptions:

- **The specification** says what its authors intend. The theorems proved
  about it and the conformance vectors are the checks on this.
- **Rocq's kernel**, and the extraction of the direct evaluator and the
  checkers to OCaml, with the OCaml compiler.
- **The chain's Wasm engine**, wasmi, follows the WebAssembly standard.
  It can be tested against WasmCert-Coq's interpreter.
- **The chain's host functions** (storage, assets, context, calls)
  implement the chain ABI. `Host/` states exactly what is assumed, so a
  chain implementation knows what it must provide.
- **Cryptographic primitives** implement their external standards.

## Cost bounds

P1 promises that the worst-case cost of every function is computable from
its types. The formalization proves the source-side bounds on iteration
and value sizes. Turning them into fuel bounds also needs the compiled
module and the chain's fuel schedule, so a phase 5 validator checks, per
module, that it stays within the bound its source implies. This is the
preservation argument the spec plan's chapter 6 asks for, and what the
roadmap's "cash in decidability" phase relies on.

## Not formalized

- Cost as a language concept: the language defines none (P4). Fuel bounds
  are checked per module, as above.
- Clarity 1–6: out of scope of the spec. Their semantics is defined by the
  legacy implementation.

## References

- Rocq libraries: [stdpp](https://github.com/rocq-iris/stdpp),
  [Equations](https://mattam82.github.io/Coq-Equations/),
  [ExtLib](https://github.com/rocq-community/coq-ext-lib),
  [WasmCert-Coq](https://github.com/WasmCert/WasmCert-Coq),
  [QuickChick](https://github.com/QuickChick/QuickChick),
  [ConCert](https://github.com/AU-COBRA/ConCert) and its typed extraction
  ([Extracting functional programs from Coq, in Coq](https://arxiv.org/abs/2108.02995)).
- Rust verification tools: [hax](https://github.com/cryspen/hax),
  [Aeneas](https://github.com/AeneasVerif/aeneas),
  [rocq-of-rust](https://github.com/formal-land/coq-of-rust).
- Wasm engine: [wasmi](https://github.com/wasmi-labs/wasmi).
- Wasm in Rust: [wasm-tools (wasm-encoder, wasmparser, wasm-smith)](https://github.com/bytecodealliance/wasm-tools),
  [Sunsetting the rustwasm GitHub org](https://blog.rust-lang.org/inside-rust/2025/07/21/sunsetting-the-rustwasm-github-org).
