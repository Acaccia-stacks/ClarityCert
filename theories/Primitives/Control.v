(** * Event and control primitives

    Semantics of spec 3.10: [print], which emits its value's rendering
    as Clarity literal text, and [panic]. *)

From ClarityVerif Require Import
  Common.Base
  Syntax.Values
  Host.Interface.
