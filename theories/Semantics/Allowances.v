(** * Asset allowances

    The allowance check of [as-contract?] and [restrict-assets?]
    (spec 2.5.9): allowance arguments evaluated before the body, coverage
    of the owner's movements, [with-all-assets-unsafe], and the reported
    allowance index (chosen by the chain ABI). *)

From ClarityCert Require Import
  Common.Base
  Syntax.Values
  Semantics.State.
