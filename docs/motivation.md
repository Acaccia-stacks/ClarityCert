# Why formalize the Clarity vNEXT specification

This document explains why the Clarity vNEXT specification
([clarity-vision](https://github.com/stx-labs/clarity-vision), pinned as
the `clarity-vision/` submodule) deserves a mechanized formalization in
Rocq, what the project delivers, and how comparable blockchains approach
the same problem.

Spec references (`P1`, `2.6.2`, ...) point to the pinned revision.
External claims cite the [sources](#sources) at the end.

## Summary

- The spec makes promises that are mathematical theorems (termination,
  bounded cost, no undefined behavior). Only a proof turns them into
  guarantees.
- The spec is a draft written "spec-first": finding its bugs now costs an
  edit, finding them after deployment costs an exploit or a migration.
- Mechanizing a specification reliably finds real bugs. It did for
  WebAssembly, which vNEXT compiles to, and for the EVM.
- Ethereum, Cardano, Tezos, Solana, Aptos, Sui and Zilliqa all invest in
  formal semantics or formal verification of their execution layer.
  Clarity has no mechanized semantics today; this project produces the
  first one.
- The compiler is in the trust path. A formal source semantics is the
  prerequisite for ever proving it correct.
- Clarity's minimal-core design makes this formalization unusually
  affordable.

## 1. The spec promises theorems

The vNEXT spec does not only describe a language. It makes universal
claims:

| Claim | Spec |
|---|---|
| Every program terminates; worst-case cost is computable from types | P1 |
| No undefined behavior, no silent failure | P7 |
| Instantiation and inline expansion terminate | 2.4.3, 2.6.2 |
| Read-only code cannot write state | 2.7.4 |
| Runtime tuples never carry fields their static type lacks | 2.3.2 |
| The standard library behaves as its documentation states | chapter 4 |

The architecture presents these properties as what Clarity adds over any
other language on the chain: "termination by construction", "complete
static analysis; tractable proofs" (architecture, section 5). A universal
claim cannot be established by examples or review alone. A mechanized
proof is what makes it a guarantee.

## 2. Now is the cheapest moment

The spec is a working draft, designed spec-first (P8): the spec is
written and reviewed before the reference compiler, and the compiler is
validated against it. The spec plan explicitly asks for a dynamic
semantics "written in a proof-friendly style (small-step or big-step
operational semantics) so verification tools can consume it", and for
typing rules "written formally enough to derive a checker from".

A defect found in a draft costs an edit. The same defect found after the
compiler ships or contracts are deployed costs a migration, or an
exploit.

Formalization also forces precision exactly where the current draft is
most delicate, for example:

- the capped least-fixpoint for fold accumulator types (2.6.2);
- call-by-name inline arguments evaluated inside `as-contract?` frames
  (2.6.3);
- a `return` that crosses an allowance frame being cancelled on violation
  (2.5.9);
- overload ambiguity when an argument has type `never` (2.6.2).

Rules like these are where informal specifications typically hide
inconsistencies.

## 3. Formalization finds real specification bugs

- **WebAssembly**, the compilation target of vNEXT: the mechanizations
  in Isabelle/HOL and Coq (WasmCert-Coq) discovered and helped fix several
  errors in the official specification, including in the type system of
  the expanded Wasm 2.0 specification.
- **Ethereum's EVM**: KEVM, an executable formal semantics in the K
  framework, revealed ambiguities and potential sources of error in the
  existing on-paper formalization (the Yellow Paper).
- **Ethereum's beacon chain**: ConsenSys's Dafny verification of the
  reference implementation uncovered several issues, with verified fixes
  proposed.

## 4. Comparable blockchains do this

| Chain | Formal work on the execution layer |
|---|---|
| Ethereum | KEVM, a complete executable semantics of the EVM that passes the official test suite and is used to verify production contracts. The beacon chain specified and verified in Dafny. Gasper finality verified with the Ethereum Foundation. A $20M Ethereum Foundation program to formally verify zkEVM components in Lean |
| Cardano | Plutus Core mechanized in Agda, with progress and preservation (type safety) proved. The ledger specification mechanized in Agda, with Agda-generated code used in the production toolchain |
| Tezos | Michelson's syntax, type system and semantics fully formalized in Coq (Mi-Cho-Coq), with a framework to verify contracts |
| Solana | A complete formal semantics of the Solana eBPF instruction set in Isabelle/HOL (OOPSLA 2025), validated against the production interpreter |
| Aptos, Sui | The Move Prover. The Aptos Framework was formally verified at scale; the Sui Prover brings it to Sui |
| Zilliqa | Scilla was designed hand in hand with a formalization of its semantics in Coq |

Cardano and Tezos are the closest analogues: a contract language designed
for verification, with a mechanized semantics in a proof assistant.
Clarity makes the same kind of promises, but no version of Clarity has a
mechanized semantics today. This project produces the first one, for
vNEXT.

## 5. The compiler is in the trust path

The architecture states it directly: "a compiler bug can make the deployed
code differ from the audited source" (architecture, section 6). Its
defenses are the spec and conformance suite, differential testing against
a direct evaluator of the spec's semantics, and reproducible builds.

The cost of a compiler bug is not hypothetical. In July 2023, a bug in
some versions of the Vyper compiler made reentrancy locks malfunction.
Several Curve pools were drained: about $69M was affected, about $52M
after white-hat recoveries. The contract source was correct; the compiled
code was not.

A formal semantics of the source language is the prerequisite for ever
proving a compiler correct. The spec plan's chapter 6 already calls for an
argument that loop bounds guaranteed by the source types survive
compilation. That theorem cannot be stated without a formal source
semantics.

## 6. What the project delivers beyond proofs

- **The first mechanized semantics of Clarity.** No version of Clarity
  has one today. The formal definition of vNEXT's types, typing rules and
  evaluation is itself a reusable artifact: the reference that tools,
  compilers and auditors can be checked against.
- **A test oracle.** An executable interpreter extracted from the Rocq
  semantics is exactly the "direct evaluator of the spec's semantics, used
  only as a test oracle" the architecture calls for to differentially
  test and fuzz the compiler (architecture, section 6).
- **Conformance vectors** whose expected outcomes are computed by the
  formal semantics, not written by hand.
- **A checked standard library.** The library is "defined by its source".
  We can prove each prelude definition does what chapter 4 says, for
  example that signed buffer conversions sign-extend.
- **Feedback to the spec.** Every ambiguity, contradiction or missing case
  found is logged in [findings.md](findings.md) and reported upstream.
- **A foundation for contract verification.** A mechanized semantics lets
  contract authors prove properties of their own contracts, as
  Mi-Cho-Coq does for Michelson.

## 7. Why this is affordable for Clarity

The spec's minimal-core design (P2) is well suited to formalization:

- about a dozen definition forms and a dozen expression forms;
- 82 primitives with uniform typing rules;
- a standard library written in the language itself, so it needs no
  separate semantics;
- no cost model in the language (P4);
- the chain ABI kept abstract, so the formalization does not wait for it.

By contrast, KEVM and Solidity semantics must model much larger and less
regular languages.

## Anticipated objections

**"The spec keeps changing."** The spec is pinned as a submodule, and
every commit pairs proofs with the exact spec revision they are about.
Modules map one-to-one to spec sections (see the mapping in the README),
so a spec change touches a predictable set of files. Feedback while the
spec is still fluid is the point.

**"Tests and the conformance suite are enough."** Tests sample behaviors;
proofs cover all of them. Termination and the absence of undefined
behavior are universal claims no finite test suite can establish. The
formalization also produces better tests (section 6).

**"Why Rocq rather than Lean, which the Ethereum Foundation uses?"** Rocq
has the closest precedents for this work: the WebAssembly mechanization
(WasmCert-Coq), Michelson (Mi-Cho-Coq), Scilla, and CompCert, the
reference for verified compilers. It also has mature extraction to an
executable interpreter, which the test oracle relies on.

## Sources

- [KEVM: A Complete Semantics of the Ethereum Virtual Machine (CSF 2018)](https://fsl.cs.illinois.edu/publications/hildenbrandt-saxena-zhu-rodrigues-daian-guth-moore-zhang-park-rosu-2018-csf)
- [Formally verifying the Ethereum 2.0 phase 0 specifications (ConsenSys)](https://consensys.io/blog/formally-verifying-the-ethereum-2-0-phase-0-specifications)
- [Formal Verification of the Ethereum 2.0 Beacon Chain (TACAS 2022)](https://link.springer.com/chapter/10.1007/978-3-030-99524-9_9)
- [Formally Verifying Finality in Gasper (Runtime Verification)](https://runtimeverification.com/blog/formally-verifying-finality-in-gasper-the-core-of-the-beacon-chain)
- [Formal verification of the zkEVM (Ethereum Foundation)](https://pq.ethereum.org/blog/formal-verification-zkevm/)
- [Advancing zkVMs with Formal Verification (Least Authority)](https://leastauthority.com/blog/advancing-zkvms-with-formal-verification/)
- [Formal specification of the Cardano blockchain ledger, mechanized in Agda (IOG)](https://www.iog.io/papers/formal-specification-of-the-cardano-blockchain-ledger-mechanized-in-agda)
- [Applying formal methods at Input Output: real-world examples](https://www.iog.io/news/applying-formal-methods-at-input-output-real-world-examples)
- [Plutus Core specification](https://plutus.cardano.intersectmbo.org/docs/delve-deeper/further-resources/plutus-core-specification)
- [Mi-Cho-Coq, a framework for certifying Tezos smart contracts](https://arxiv.org/abs/1909.08671)
- [A Complete Formal Semantics of eBPF Instruction Set Architecture for Solana (OOPSLA 2025)](https://2025.splashcon.org/details/OOPSLA/2/A-complete-formal-semantics-of-eBPF-instruction-set-architecture-for-Solana)
- [Formal verification with the Move Prover (Aptos)](https://aptos.dev/build/smart-contracts/prover)
- [Sui Prover: bringing formal verification to Sui](https://blog.sui.io/asymptotic-move-prover-formal-verification/)
- [Scilla: a Smart Contract Intermediate-Level LAnguage](https://arxiv.org/pdf/1801.00687)
- [Designing and Maintaining an Efficient WebAssembly Mechanisation](https://vtss.doc.ic.ac.uk/publications/Rao2025Designing.html)
- [Progressful Interpreters for Efficient WebAssembly Mechanisation (POPL 2025)](https://popl25.sigplan.org/details/POPL-2025-popl-research-papers/22/Progressful-Interpreters-for-Efficient-WebAssembly-Mechanisation)
- [Vyper incident analysis (CertiK)](https://www.certik.com/blog/vyper-incident-anaylsis)
- [Curve Finance liquidity pools hack explained (Hacken)](https://hacken.io/discover/curve-finance-liquidity-pools-hack-explained/)
