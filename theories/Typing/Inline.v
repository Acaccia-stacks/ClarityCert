(** * Inline expansion

    Call-by-name expansion of [define-inline] functions (spec 2.6.3):
    hygiene, [return] targeting the caller, the at-most-once rule for
    value parameters. *)

From ClarityVerif Require Import
  Common.Base
  Syntax.Ast.
