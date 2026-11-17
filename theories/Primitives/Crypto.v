(** * Cryptographic primitives

    Semantics of spec 3.6 in terms of the abstract standards of
    [Host.Crypto]. [hash160] is a prelude definition over [ripemd160] and
    [sha256]. *)

From ClarityCert Require Import
  Common.Base
  Syntax.Values
  Host.Crypto.
