(** * Cryptographic standards

    Hash functions and signature schemes are external standards (layering
    rule test 3). They are abstract parameters here, with only the
    properties the spec relies on (output lengths, low-S canonicity). *)

From ClarityVerif Require Import
  Common.Base.
