(** * Host interface

    The host functions the semantics is parameterized by: storage, assets,
    transaction context, chain-data lookups (total, spec 3.9), contract
    calls, events. Every primitive that passes the host-access test of the
    layering rule is defined in terms of this interface. *)

From ClarityVerif Require Import
  Common.Base
  Syntax.Types
  Syntax.Values
  Host.Abi
  Host.Crypto.
