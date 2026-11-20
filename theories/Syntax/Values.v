(** * Values

    Runtime values and the value-has-type relation. Values carry no static
    type information (spec 2.7.1); tuples have exactly the fields of their
    type (2.3.2). *)

From ClarityCert Require Import
  Common.Base
  Syntax.Types.

From Stdlib Require Import Eqdep_dec.

(** ** Integers

    [int] values are signed 128-bit integers and [uint] values unsigned
    ones (spec 2.3.1). A literal outside the range is a parse error
    (2.2), and an operation whose result falls outside is a runtime error
    (3.1), so every integer value is in range. As for principals
    ([Syntax.Types]), the range is part of the representation: an
    integer is a [Z] with a boolean proof that it lies within the bounds,
    and two integers are equal when their [Z]s are ([bounded_ext]).

    [bounded lo hi] is the integers from [lo] to [hi], both included;
    [int128] and [uint128] are its two instances. Arithmetic computes on
    [Z] and comes back through [bounded_of_Z], which is [None] out of
    range: that [None] is the overflow error of the primitives. *)

Local Open Scope Z_scope.

Definition int_min : Z := - 2 ^ 127.
Definition int_max : Z := 2 ^ 127 - 1.
Definition uint_max : Z := 2 ^ 128 - 1.

Definition in_range (lo hi z : Z) : bool := (lo <=? z) && (z <=? hi).

Record bounded (lo hi : Z) := {
  bval : Z;
  bwf : in_range lo hi bval = true;
}.

Arguments bval {lo hi}.
Arguments bwf {lo hi}.

Definition int128 : Type := bounded int_min int_max.
Definition uint128 : Type := bounded 0 uint_max.

Lemma bounded_ext {lo hi : Z} (x y : bounded lo hi) :
  bval x = bval y -> x = y.
Proof.
  destruct x as [v wf], y as [v' wf']; simpl; intros ->.
  f_equal. apply UIP_dec, bool_dec.
Qed.

Lemma bounded_range {lo hi : Z} (x : bounded lo hi) :
  (lo <= bval x <= hi).
Proof.
  destruct x as [v wf]; simpl. unfold in_range in wf.
  apply andb_prop in wf as [H1 H2].
  apply Z.leb_le in H1, H2. lia.
Qed.

Lemma bounded_eq_dec {lo hi : Z} (x y : bounded lo hi) :
  {x = y} + {x <> y}.
Proof.
  destruct (Z.eq_dec (bval x) (bval y)) as [H | H].
  - left. now apply bounded_ext.
  - right. intros ->. now apply H.
Defined.

(** The integer [z], if it is in range. *)
Definition bounded_of_Z (lo hi z : Z) : option (bounded lo hi) :=
  match bool_dec (in_range lo hi z) true with
  | left H => Some {| bval := z; bwf := H |}
  | right _ => None
  end.

Lemma bounded_of_Z_val (lo hi z : Z) (x : bounded lo hi) :
  bounded_of_Z lo hi z = Some x -> bval x = z.
Proof.
  unfold bounded_of_Z. destruct (bool_dec _ true); [| discriminate].
  now intros [= <-].
Qed.

Lemma bounded_of_Z_none (lo hi z : Z) :
  bounded_of_Z lo hi z = None <-> ~ (lo <= z <= hi).
Proof.
  unfold bounded_of_Z, in_range.
  destruct (bool_dec _ true) as [H | H]; split; try easy.
  - (* In range, so not out of range. *)
    intros Hz. exfalso. apply Hz.
    apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2. lia.
  - (* Out of range, so the bounds fail. *)
    intros _ Hz. apply H, andb_true_intro.
    split; apply Z.leb_le; lia.
Qed.

Lemma bounded_of_Z_bval (lo hi : Z) (x : bounded lo hi) :
  bounded_of_Z lo hi (bval x) = Some x.
Proof.
  unfold bounded_of_Z. destruct (bool_dec _ true) as [H | H].
  - f_equal. now apply bounded_ext.
  - destruct x as [v wf]. contradiction.
Qed.

(** The bounds of [int] and [uint]. One past either end of [int] is out
    of range, and so is [-1] as a [uint]. *)
Example integer_examples :
  option_map bval (bounded_of_Z int_min int_max int_max) = Some int_max
  /\ bounded_of_Z int_min int_max (int_max + 1) = None
  /\ bounded_of_Z int_min int_max (int_min - 1) = None
  /\ option_map bval (bounded_of_Z 0 uint_max uint_max) = Some uint_max
  /\ bounded_of_Z 0 uint_max (-1) = None.
Proof. repeat split. Qed.
