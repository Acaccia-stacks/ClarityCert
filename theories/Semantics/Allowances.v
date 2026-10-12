(** * Asset allowances

    The allowance check of [as-contract?] and [restrict-assets?]
    (spec 2.5.9): coverage of the owner's movements and the index of the
    first violated allowance. *)

From ClarityVerif Require Import
  Common.Base
  Syntax.Values
  Semantics.State.
