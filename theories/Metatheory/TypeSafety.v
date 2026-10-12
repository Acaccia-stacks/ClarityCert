(** * Type safety

    Evaluation of a well-typed instance yields a value of its static type,
    an early [return], or an abort; never a stuck state (spec 2.7.1, P7). *)

From ClarityVerif Require Import
  Common.Base
  Typing.Typing
  Typing.StaticChecks
  Semantics.Eval.
