(** * Arithmetic and comparison primitives

    Semantics of spec 3.1 and 3.2: 128-bit [int]/[uint] arithmetic with
    overflow aborts, bitwise operations, shifts, comparisons (element-wise
    order on sequences), [is-eq]. *)

From ClarityVerif Require Import
  Common.Base
  Syntax.Values.
