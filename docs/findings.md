# Findings

Issues found in the specification while formalizing it
(ambiguities, inconsistencies, unsound rules, missing cases).

Spec revisions are clarity-vision commits.

| # | Spec section | Description | Status |
|---|--------------|-------------|--------|
| 1 | Spec plan, conformance suite ("What a vector deliberately does not pin") | A compile-error vector names "the class of error", but nothing says which class is reported when a contract has several errors (for example an arity error in one function and a read-only violation in another). Two conforming compilers may report different classes for the same contract, so a vector containing such a contract has no single expected outcome, and the Rust and Rocq front ends cannot be compared on it. Needs a rule: a defined checking order, or vectors restricted to contracts with exactly one error, with any of the errors accepted otherwise. | Open (checked at b387226) |
| 2 | 03 §3.11 | The count table lists 9 conversions, but §3.4 lists 8 (`buff-to-uint-be`, the four `*-to-buff-*`, `to-consensus-buff`, `from-consensus-buff?`, `get-bitcoin-tx-output?`). The total is 70, not 71. | Open (checked at b387226) |
| 3 | 02 §2.6.5 | Typo: "Insides the body" should be "Inside the body". | Open (checked at b387226) |
| 4 | Architecture §4 | The host-function table still uses the legacy context names (tx-sender, contract-caller, current contract) instead of the `sender`, `caller` and `contract` fields of `get-current-context` (03 §3.9), and lists Bitcoin transaction output parsing under chain data, while 03 §3.4 moved it to the conversions as pure parsing, not a chain lookup. | Open (checked at b387226) |
| 5 | 02 §2.3.2 | Structural sub-traits make `<:` a preorder, not a partial order: two traits `X` and `Y` with the same functions satisfy `(trait X) <: (trait Y)` and `(trait Y) <: (trait X)`. The join rule then gives `lub((trait X), (trait Y))` two answers, `(trait X)` and `(trait Y)`, which differ in the interface emitted for a public function's result type (2.6.4). Needs a tie-break, or equality of trait types up to equivalence. | Open (checked at b387226) |
| 6 | 02 §2.6.2 | An overloaded name passed as a `(function ...)` argument has no "exactly one overload" rule: the rule says the named function MUST admit an instantiation, not which overload is chosen when several do. In the capped fold fixpoint, different steps could even select different overloads as the accumulator type grows. | Open (checked at b387226) |
| 7 | 02 §2.5.3, §2.6.4; chain ABI | Typing of `never`: a `match` on a scrutinee of type `never` (or with a `never` component), whether dead arms contribute to the `match` lub, a public function whose inferred result type contains `never`, and the serialized size of `never`. Reported upstream as [clarity-vision#20](https://github.com/stx-labs/clarity-vision/issues/20). | Open (checked at b387226) |
