(** * Asset primitives

    Semantics of spec 3.8: fungible and non-fungible tokens and STX, with
    their [err] codes; every movement is recorded in the asset map. *)

From ClarityCert Require Import
  Common.Base
  Syntax.Values
  Host.Interface.
