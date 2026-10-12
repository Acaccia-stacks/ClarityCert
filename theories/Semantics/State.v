(** * Execution state

    Local environments, nested state frames with commit/rollback, the
    transaction asset map, and the event batch (spec 2.7.3, 2.7.6). *)

From ClarityVerif Require Import
  Common.Base
  Syntax.Values
  Host.Interface.
