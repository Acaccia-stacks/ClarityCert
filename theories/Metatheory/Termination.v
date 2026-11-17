(** * Termination

    Every well-formed contract terminates, and macro expansion and
    instantiation terminate (P1, spec 2.4.3). *)

From ClarityCert Require Import
  Common.Base
  Typing.Instantiation
  Typing.Macros
  Typing.StaticChecks
  Semantics.Eval.
