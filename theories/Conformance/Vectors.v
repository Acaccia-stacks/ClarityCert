(** * Conformance vectors

    Concrete contracts with their expected outcome (compile error class,
    results, events, aborts), mirroring the spec's language vectors. *)

From ClarityVerif Require Import
  Common.Base
  Std.Prelude
  Typing.Typing
  Semantics.Eval.
