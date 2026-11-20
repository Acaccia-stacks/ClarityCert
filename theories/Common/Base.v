(** * Base

    Shared Rocq imports, notations and generic lemmas used across the
    development. Every other module imports this one first. Not to be
    confused with the Clarity standard library prelude ([Std.Prelude]). *)

From Stdlib Require Export
  Bool
  NArith
  ZArith
  String
  List
  Lia.

Export ListNotations.

From Stdlib Require Import Eqdep_dec.

(** ** Refinements

    [refined p] is the values [x] with [p x = true]: a value together with
    a boolean proof. Integers, string characters and other values whose
    rules hold of every value use it, so an invalid one cannot be
    represented. Because the proof is an equation between booleans, any
    two proofs are equal ([UIP_dec]), so two refined values are equal
    when their values are ([refined_ext]), with no axiom. *)

Record refined {A : Type} (p : A -> bool) := {
  rval : A;
  rwf : p rval = true;
}.

Arguments rval {A p}.
Arguments rwf {A p}.

Lemma refined_ext {A : Type} {p : A -> bool} (x y : refined p) :
  rval x = rval y -> x = y.
Proof.
  destruct x as [a wf], y as [b wf']; simpl; intros ->.
  f_equal. apply UIP_dec, bool_dec.
Qed.

(** Decided by comparing the values, so it computes when [eq_dec]
    does. *)
Lemma refined_eq_dec {A : Type} {p : A -> bool}
  (eq_dec : forall a b : A, {a = b} + {a <> b}) (x y : refined p) :
  {x = y} + {x <> y}.
Proof.
  destruct (eq_dec (rval x) (rval y)) as [H | H].
  - left. now apply refined_ext.
  - right. intros ->. now apply H.
Defined.

(** [a] as a refined value, if [p a] holds. *)
Definition refined_of {A : Type} (p : A -> bool) (a : A) : option (refined p) :=
  match bool_dec (p a) true with
  | left H => Some {| rval := a; rwf := H |}
  | right _ => None
  end.

Lemma refined_of_rval {A : Type} (p : A -> bool) (a : A) (x : refined p) :
  refined_of p a = Some x -> rval x = a.
Proof.
  unfold refined_of. destruct (bool_dec _ true); [| discriminate].
  now intros [= <-].
Qed.

Lemma refined_of_none {A : Type} (p : A -> bool) (a : A) :
  refined_of p a = None <-> p a = false.
Proof.
  unfold refined_of. destruct (bool_dec _ true) as [H | H].
  - split; [discriminate | congruence].
  - apply not_true_is_false in H. now rewrite H.
Qed.

Lemma refined_of_self {A : Type} (p : A -> bool) (x : refined p) :
  refined_of p (rval x) = Some x.
Proof.
  unfold refined_of. destruct (bool_dec _ true) as [H | H].
  - f_equal. now apply refined_ext.
  - destruct x as [a wf]. contradiction.
Qed.
