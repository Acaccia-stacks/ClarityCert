(** * Base

    Shared Rocq imports, notations and generic lemmas used across the
    development. Every other module imports this one first. Not to be
    confused with the Clarity standard library prelude ([Std.Prelude]). *)

From Stdlib Require Export
  Bool
  NArith
  ZArith
  String
  List.

Export ListNotations.
