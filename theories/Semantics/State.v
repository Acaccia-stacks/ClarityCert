(** * Execution state

    Local environments, nested state frames with commit/rollback (opened
    by every public function invocation, [as-contract?] and
    [restrict-assets?]), the transaction asset map, and the event batch,
    whose discarded events stop counting toward the transaction's event
    bytes (spec 2.5.9, 2.7.3, 2.7.6). *)

From ClarityVerif Require Import
  Common.Base
  Syntax.Values
  Host.Interface.
