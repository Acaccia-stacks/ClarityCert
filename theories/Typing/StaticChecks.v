(** * Static checks

    Contract-level static rules: acyclic definition graph (spec 2.4.3), no
    shadowing (2.5.2), intermediate responses handled (2.4.1), no [return]
    at top level (2.4.2), [impl-trait] conformance, read-only enforcement
    (2.7.4), prelude names reserved (2.4.5). *)

From ClarityVerif Require Import
  Common.Base
  Syntax.Ast
  Typing.Typing.
