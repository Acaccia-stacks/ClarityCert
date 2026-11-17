(** * Host interface

    The runtime layer of the chain ABI the semantics is parameterized by
    ([clarity-vision/07-chain-abi.md]): an untyped key-value store (4.2),
    assets, transaction context and chain-data lookups (6.2, total by
    spec 3.9), contract calls with the [read_only] and result flags (5.3),
    state frames (2.7.3), events (contract events emitted by their index
    in the interface, with their name and data; asset events; the size of
    each and the transaction's event-byte cap, 8.3), [log] output, which
    the chain discards (6.2), and [abort] with a runtime error class
    (10.2). Every primitive that passes the host-access test of the
    layering rule is defined in terms of this interface. *)

From ClarityCert Require Import
  Common.Base
  Syntax.Types
  Syntax.Values
  Host.Abi
  Host.Crypto.
