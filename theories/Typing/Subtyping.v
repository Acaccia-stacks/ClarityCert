(** * Subtyping

    The subtyping preorder and the join (spec 2.3.2): contract-literal
    types, structural sub-traits and equivalent traits, the join among
    principal-like types (two distinct equivalent traits join to
    [principal]), the join of a set taken as a whole rather than as a
    pairwise fold, and the "meet" relation used by overload checks. With
    equivalent traits, the join is not a least upper bound in the
    order-theoretic sense. *)

From ClarityCert Require Import
  Common.Base
  Syntax.Types.
