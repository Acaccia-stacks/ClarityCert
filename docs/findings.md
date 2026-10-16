# Findings

Issues found in the specification while formalizing it
(ambiguities, inconsistencies, unsound rules, missing cases).

Spec revisions are clarity-vision commits.

| # | Spec section | Description | Status |
|---|--------------|-------------|--------|
| 1 | Spec plan, conformance suite ("What a vector deliberately does not pin") | A compile-error vector names "the class of error", but nothing says which class is reported when a contract has several errors (for example an arity error in one function and a read-only violation in another). Two conforming compilers may report different classes for the same contract, so a vector containing such a contract has no single expected outcome, and the Rust and Rocq front ends cannot be compared on it. Needs a rule: a defined checking order, or vectors restricted to contracts with exactly one error, with any of the errors accepted otherwise. | Open (checked at b387226) |
