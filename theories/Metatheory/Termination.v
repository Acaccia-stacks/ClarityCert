(** * Termination

    Every well-formed contract terminates, and inline expansion and
    instantiation terminate (P1, spec 2.4.3). *)

From ClarityVerif Require Import
  Common.Base
  Typing.Instantiation
  Typing.Inline
  Typing.StaticChecks
  Semantics.Eval.
