# Formalizing Clarity vNEXT: why, what and how

This document explains why the Clarity vNEXT specification
([clarity-vision](https://github.com/stx-labs/clarity-vision), pinned as
the `clarity-vision/` submodule) deserves a mechanized formalization in
Rocq, how the work divides between Rocq and the Rust production compiler,
in which order it should happen, and what it gives to the people who
build and use Clarity contracts. The technical design behind each step is
in [design.md](design.md).

Spec references (`P1`, `2.6.2`, ...) point to the pinned revision.
External claims cite the [sources](#sources) at the end.

## Summary

- **Why.** The spec makes promises that are mathematical theorems
  (termination, bounded cost, no undefined behavior), and the compiler is
  in the trust path. Only proofs turn these promises into guarantees, and
  a draft spec is the cheapest place to find their flaws. Ethereum,
  Cardano, Tezos, Solana, Aptos, Sui and Zilliqa all invest in formal
  semantics or verification; Clarity has none today.
- **What.** Rocq holds the reference: the formal semantics, the proofs
  about it, and executable checkers extracted from it. Rust holds the
  product: the production compiler, tested, validated and, for critical
  parts, proved against the Rocq reference. Rocq never enters the
  production path.
- **How.** In five phases tied to the spec's progress: formal spec,
  executable reference, metatheory, compilation, then selective proofs of
  Rust code and user tooling. Each phase pays off on its own.
- **Benefits.** A spec without ambiguities, a Rust compiler that is tested
  against the spec from its first day, an end-to-end guarantee that a
  deployed module behaves as its source says, and the ability for contract
  authors and auditors to prove properties of real contracts.

# Part I. Why

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

The spec is a working draft, designed spec-first (P8): it is written and
reviewed before the compiler, and the compiler is validated against it.
The spec plan explicitly asks for a dynamic semantics "written in a
proof-friendly style (small-step or big-step operational semantics) so
verification tools can consume it", and for typing rules "written
formally enough to derive a checker from".

A defect found in a draft costs an edit. The same defect found after the
compiler ships or contracts are deployed costs a migration, or an exploit.
Formalization forces precision exactly where the draft is most delicate:
the capped fixpoint for fold accumulator types (2.6.2), call-by-name
inline arguments evaluated inside `as-contract?` frames (2.6.3), a
`return` crossing an allowance frame (2.5.9), the typing of `never`.

Mechanizing a specification reliably finds real bugs:

- **WebAssembly**, the compilation target of vNEXT: the mechanizations in
  Isabelle/HOL and Coq (WasmCert-Coq) discovered and helped fix several
  errors in the official specification, including in the type system of
  Wasm 2.0.
- **Ethereum's EVM**: KEVM, an executable formal semantics in the K
  framework, revealed ambiguities and potential sources of error in the
  Yellow Paper.
- **Ethereum's beacon chain**: ConsenSys's Dafny verification of the
  reference implementation uncovered several issues.

## 3. Comparable blockchains do this

| Chain | Formal work on the execution layer |
|---|---|
| Ethereum | KEVM, a complete executable semantics of the EVM that passes the official test suite and is used to verify production contracts. The beacon chain verified in Dafny. Gasper finality verified with the Ethereum Foundation. A $20M Ethereum Foundation program to formally verify zkEVM components in Lean |
| Cardano | Plutus Core mechanized in Agda, with type safety proved. The ledger specification mechanized in Agda, with Agda-generated code used in the production toolchain |
| Tezos | Michelson's syntax, type system and semantics fully formalized in Coq (Mi-Cho-Coq), with a framework to verify contracts |
| Solana | A complete formal semantics of the Solana eBPF instruction set in Isabelle/HOL (OOPSLA 2025), validated against the production interpreter |
| Aptos, Sui | The Move Prover. The Aptos Framework was formally verified at scale; the Sui Prover brings it to Sui |
| Zilliqa | Scilla was designed hand in hand with a formalization of its semantics in Coq |

Cardano and Tezos are the closest analogues: a contract language designed
for verification, with a mechanized semantics in a proof assistant.
Clarity makes the same kind of promises, but no version of Clarity has a
mechanized semantics today. This project produces the first one.

## 4. The compiler is in the trust path

The architecture states it directly: "a compiler bug can make the deployed
code differ from the audited source" (architecture, section 6). The cost
is not hypothetical. In July 2023, a bug in some versions of the Vyper
compiler made reentrancy locks malfunction. Several Curve pools were
drained: about $69M was affected, about $52M after white-hat recoveries.
The contract source was correct; the compiled code was not.

A formal semantics of the source language is the prerequisite for ever
checking a compiler beyond testing. The spec plan's chapter 6 already
calls for an argument that loop bounds guaranteed by the source types
survive compilation. That theorem cannot be stated without a formal
source semantics.

# Part II. The plan

## 5. Rocq is the reference, Rust is the product

The production compiler is written in Rust, following the crates sketched
in the architecture (section 2). The Rocq project does not compete with
it. It is the reference the compiler is checked against, and it stays out
of the production path.

| Component | Rocq (reference) | Rust (product) |
|---|---|---|
| Language definition | Formal syntax, types, typing rules, dynamic semantics | Implements them |
| Parser | Reference parser, proved to round-trip | Production parser (`clarity-syntax`) |
| Type checking and instantiation | Reference checker proved equal to the typing rules, also used to check the Rust front end's results | Production checker with good error messages (`clarity-types`) |
| Standard library | Proofs that each prelude definition behaves as documented | Compiles the prelude source (`clarity-std`) |
| Evaluation | Direct evaluator, extracted as the test oracle | None: the compiler is the only production implementation |
| Compilation to Wasm | Translation validator, proved correct | Production compiler (`clarity-compiler`) |
| Verification of deployments | The validator | `clarity-verify` rebuilds a module and runs the validator |
| Contract verification | Program logic for proofs about contracts | None |

"Reference" means the reference the Rust compiler is checked against, not
an authority over the spec: the prose spec stays normative, and a
disagreement between the two is a finding settled in the spec
([findings.md](findings.md)).

## 6. How the Rust compiler is checked

The Rust compiler is checked against the Rocq reference at four
increasing levels of assurance, adopted in order:

1. **Testing.** Conformance vectors whose outcomes are computed by the
   formal semantics, differential testing and fuzzing against the direct
   evaluator, and a comparison of the Rust and Rocq type checkers on every
   test contract.
2. **Checking the front end.** For each contract, the Rust type checker
   exports its decisions (instances, types, resolved calls), and the Rocq
   checker confirms they are exactly what the typing rules prescribe.
3. **Translation validation.** A validator proved correct in Rocq
   confirms that each module the Rust compiler emits behaves as its
   source. The compiler itself stays unverified, but every validated
   contract gets the end-to-end guarantee of section 8.
4. **Proving Rust code.** For the most critical code, tools that translate
   Rust into a proof assistant (hax, Aeneas, rocq-of-rust) allow proving
   the Rust source itself equal to the Rocq definitions, as the Ethereum
   Foundation's zkEVM program does for production Rust libraries.

[design.md](design.md) describes each level: what the Rust code exports,
how it is compared, and the libraries on both sides.

## 7. Order of work

The order follows the spec: each phase starts when the chapters it relies
on are stable enough.

| Phase | Starts when | Rocq | Rust | Benefit |
|---|---|---|---|---|
| 1. Formal spec | Now (draft chapters 2 to 4) | Syntax, types, subtyping, typing rules, semantics of core forms and primitives, abstract host | Not required | Spec findings fixed before any compiler depends on them |
| 2. Executable reference | Grammar and typing rules settled | Executable parser, type checker and evaluator, extracted as the direct evaluator; vector outcomes | Front end (`clarity-syntax`, `clarity-types`) developed against the direct evaluator and the vectors | The Rust compiler is tested against the spec from its first line |
| 3. Metatheory | In parallel with phase 2 | Type safety, termination, determinism, read-only safety, uniqueness of typing, prelude properties | None | The spec's promises become theorems |
| 4. Compilation | Spec chapter 6 and chain ABI written | Wasm semantics, translation validator, front-end checker | `clarity-compiler`, `clarity-verify`; export of front-end results | End-to-end guarantee for every validated contract |
| 5. Selective proofs and tooling | After phase 4 | Program logic for contracts; checking of cost bounds per module | Proofs of critical crates | Proved compiler components; contract authors can prove their own contracts |

One dependency crosses phases: if critical Rust crates may be proved in
phase 5, they must be written within the subset of Rust the verification
tools support from phase 2 onward. Deciding which crates this applies to
is a phase 2 decision.

## 8. The end result

With phases 1 to 4 in place, every validated contract satisfies one
theorem, stated informally:

> For any source text, if the front end accepts it and its module is
> validated, then for every chain state and every call, running the
> module under the WebAssembly semantics, with host functions that
> satisfy the chain ABI, produces the same results, events, asset
> movements and aborts as the Clarity semantics of the source, and
> terminates within bounds that follow from the source's types.

What remains trusted is the spec's intent, the proof assistant, the
chain's Wasm engine and host functions, and the cryptographic standards
([design.md](design.md) details each). That is a much smaller base than
today's, where the compiler, every library function and every informal
rule must be trusted.

# Part III. Benefits

## 9. Who benefits

**Spec authors** get every ambiguity and contradiction reported with a
precise location ([findings.md](findings.md)), and can check any proposed
change by rerunning the proofs: a change that breaks type safety or
termination is caught before it is merged.

**The compiler team** gets a spec without ambiguities to implement,
conformance vectors whose outcomes are computed rather than written by
hand, the direct evaluator the architecture requires as a test oracle
for differential testing and fuzzing (architecture, section 6), and later
a validator that turns each compilation into a checked one.

**Contract authors** can:

- rely, without proving anything, on the language-level theorems
  (termination, read-only safety, no undefined behavior) and on the
  proved behavior of every standard library function;
- run their contracts on the direct evaluator during development, to see
  what the formal semantics gives for a contract, which is the behavior
  the compiler is tested against;
- prove properties of their own contracts against the formal
  semantics: that a token's total supply is conserved, that only an owner
  can call an administrative function, that an `as-contract?` frame cannot
  move more than its allowances, that a function never returns `err`;
- do so in Rocq, or through tools built on the program logic that hide the
  proof assistant for common properties, such as the verification
  annotations (invariants, pre- and postconditions) the spec plan lists as
  a design opportunity.

**Auditors** can work at the source level and know their conclusions hold
for the deployed code. The architecture already ties analyses to the
triple of source hash, compiler version and module hash (section 6 of the
architecture); with validated compilation, a proof about the source is a
proof about the module on chain.

**Wallets and explorers** can show, next to a contract's verified source,
which of its properties are proved, and that the proof applies to the
deployed module.

**Tool builders** can prove static analyzers, cost analyzers and linters
sound against the same semantics, instead of each tool embedding its own
interpretation of the language.

## 10. Why this is affordable for Clarity

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
formalization also produces the tests: vector outcomes and the direct
evaluator.

**"We are writing the compiler in Rust anyway."** The Rocq project does not
replace it; it is what the Rust compiler is tested, validated and, where
it matters, proved against (sections 5 and 6). Rocq never enters the
production path.

**"End-to-end verification is unrealistic."** It is not the entry price.
Phases 1 to 3 are bounded work on a deliberately small language, and each
pays off alone. Compilation is covered by validating each compiled
module, without verifying the compiler. CompCert and CakeML show that
even fully verified compilers are achievable.

**"Why Rocq rather than Lean, which the Ethereum Foundation uses?"** Rocq
has the closest precedents for this work: the WebAssembly mechanization
(WasmCert-Coq), Michelson (Mi-Cho-Coq), Scilla, and CompCert, the
reference for verified compilers. It has mature extraction to executable
code, which the direct evaluator relies on, and hax translates Rust to
Rocq. If proofs of Rust code become central in phase 5, Aeneas's more
mature Lean backend is the main argument for Lean, and the choice of tool
for that phase can be revisited without affecting phases 1 to 4.

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
- [CompCert: a formally verified C compiler](https://compcert.org/)
- [CakeML: a verified implementation of ML](https://cakeml.org/)
- [Vyper incident analysis (CertiK)](https://www.certik.com/blog/vyper-incident-anaylsis)
- [Curve Finance liquidity pools hack explained (Hacken)](https://hacken.io/discover/curve-finance-liquidity-pools-hack-explained/)
- Rust verification tools: [hax (Cryspen)](https://github.com/cryspen/hax), [Aeneas](https://github.com/AeneasVerif/aeneas), [rocq-of-rust (Formal Land)](https://github.com/formal-land/coq-of-rust)
