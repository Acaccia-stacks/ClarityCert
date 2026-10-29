(** * Principal primitives

    Semantics of spec 3.5: [principal-to-ascii] and [contract-hash?].
    [principal-construct?] and [principal-destruct?] are prelude
    definitions. *)

From ClarityVerif Require Import
  Common.Base
  Syntax.Values
  Host.Interface.
