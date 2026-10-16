(** * Conversion and serialization primitives

    Semantics of spec 3.4: integer/buffer conversions with a size-term
    width, consensus serialization through the ABI wire format, and
    Bitcoin transaction parsing ([get-bitcoin-tx-output?]). *)

From ClarityVerif Require Import
  Common.Base
  Syntax.Values
  Host.Abi.
