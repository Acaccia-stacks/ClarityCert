(** * Context and chain-data primitives

    Semantics of spec 3.9: the [get-current-context] record, with its
    frame-scoped [sender], [caller] and [contract] fields, and the total
    chain-data lookups. *)

From ClarityCert Require Import
  Common.Base
  Syntax.Values
  Host.Interface.
