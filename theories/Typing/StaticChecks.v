(** * Static checks

    Contract-level static rules: version declaration first (spec 2.4.0);
    acyclic definition graph over names, checked before instantiation
    (2.4.3); definitions used at deploy come first and no [return] at top
    level (2.4.2); keywords never bound, reserved names and prelude names
    never redefined, no shadowing (2.2, 2.4.5, 2.5.2); intermediate
    responses handled and [impl-trait] conformance (2.4.1); read-only
    enforcement (2.7.4). *)

From ClarityVerif Require Import
  Common.Base
  Syntax.Ast
  Typing.Typing.
