(** * Macros

    Expansion of [define-macro] definitions (spec 2.6.3): resolution and
    typing as for a private function, with each parameter at its declared
    type; call-by-name evaluation; hygiene; [return] targeting the caller;
    the at-most-once rule for value parameters. *)

From ClarityVerif Require Import
  Common.Base
  Syntax.Ast.
