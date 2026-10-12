(** * Chain ABI

    The parts of the chain ABI the language spec refers to without defining:
    the value wire format and [serialized-size] (SIP-005), contract
    interfaces, and trait implementation by an interface. Kept abstract
    until the ABI document exists. *)

From ClarityVerif Require Import
  Common.Base
  Syntax.Types
  Syntax.Values.
