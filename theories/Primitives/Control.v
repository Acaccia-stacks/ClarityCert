(** * Event and control primitives

    Semantics of spec 3.10: [emit], which emits the canonical encoding of
    its value as an event of a [define-event] or an [(event T)]
    reference; [log], debug output the chain discards; and [panic]. *)

From ClarityCert Require Import
  Common.Base
  Syntax.Values
  Host.Interface.
