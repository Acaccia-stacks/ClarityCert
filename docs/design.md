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

## Not formalized (yet)

- Parsing: the spec has no complete EBNF yet. `Syntax/Lexical.v` covers
  the lexical well-formedness rules that are stated (2.2).
- Compilation to Wasm (plan chapter 6): not written. It would become a
  `Compiler/` directory with a semantics-preservation theorem.
- Cost: the language defines none (P4).
