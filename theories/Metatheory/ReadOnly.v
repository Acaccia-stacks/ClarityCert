(** * Read-only safety

    A function accepted by the read-only check performs no state writes
    (spec 2.7.4). *)

From ClarityVerif Require Import
  Common.Base
  Typing.StaticChecks
  Semantics.Eval.
