(** * Language limits

    Language-level limits (spec 2.8): value and intermediate size limits,
    fixpoint step limit, type depth, identifier length, function call
    depth within a contract, allowances per frame, storage key size,
    [print] message size. The contract-call depth limit belongs to the
    chain ABI. *)

From ClarityVerif Require Import
  Common.Base.
