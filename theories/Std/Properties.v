(** * Standard library properties

    The prelude is well-typed, and each definition behaves as chapter 4
    and its disposition table claim (e.g. [unwrap!] early exit, [pow],
    [sqrti], signed buffer conversions sign-extend). *)

From ClarityVerif Require Import
  Common.Base
  Std.Prelude
  Typing.Typing
  Typing.StaticChecks
  Semantics.Eval.
