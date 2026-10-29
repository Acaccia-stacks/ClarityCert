(** * Static checks

    Contract-level static rules: version declaration first (spec 2.4.0);
    acyclic definition graph over names, checked before instantiation
    (2.4.3); definitions used at deploy come first and no [return] at top
    level (2.4.2); keywords never bound, reserved names and prelude names
    never redefined, no shadowing (2.2, 2.4.5, 2.5.2); intermediate
    responses handled and [impl-trait] conformance against declared
    signatures (2.4.1, 2.5.8); overloads that do not overlap (2.6.2); the
    function call depth limit, enforced statically (2.7.5, 2.8);
    read-only enforcement (2.7.4). *)

From ClarityVerif Require Import
  Common.Base
  Syntax.Ast
  Typing.Typing.
