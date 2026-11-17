(** * Determinism

    Evaluation is a function of the instance, the host state and the
    transaction context. Typing is unique: a contract has at most one
    elaboration (instances, substitutions, types), so the type checker is
    a function from source to elaboration or error (spec 2.6.2). *)

From ClarityCert Require Import
  Common.Base
  Typing.Typing
  Typing.StaticChecks
  Semantics.Eval.
