(** * Values

    Runtime values and the value-has-type relation. Values carry no static
    type information (spec 2.7.1); tuples have exactly the fields of their
    type (2.3.2). *)

From ClarityCert Require Import
  Common.Base
  Syntax.Lexical
  Syntax.Types.

(** ** Integers

    [int] values are signed 128-bit integers and [uint] values unsigned
    ones (spec 2.3.1). A literal outside the range is a parse error
    (2.2), and an operation whose result falls outside is a runtime error
    (3.1), so every integer value is in range. The range is part of the
    representation: [bounded lo hi] is the [Z]s from [lo] to [hi], both
    included, as a refinement ([Common.Base]), and [int128] and [uint128]
    are its two instances. Arithmetic computes on [Z] and comes back
    through [bounded_of_Z], which is [None] out of range: that [None] is
    the overflow error of the primitives. *)

Section Integers.

Local Open Scope Z_scope.

Definition int_min : Z := - 2 ^ 127.
Definition int_max : Z := 2 ^ 127 - 1.
Definition uint_max : Z := 2 ^ 128 - 1.

Definition in_range (lo hi z : Z) : bool := (lo <=? z) && (z <=? hi).

Lemma in_range_spec (lo hi z : Z) :
  in_range lo hi z = true <-> lo <= z <= hi.
Proof.
  unfold in_range. rewrite andb_true_iff, !Z.leb_le. reflexivity.
Qed.

Definition bounded (lo hi : Z) : Type := refined (in_range lo hi).
Definition bounded_of_Z (lo hi z : Z) : option (bounded lo hi) :=
  refined_of (in_range lo hi) z.

Definition int128 : Type := bounded int_min int_max.
Definition uint128 : Type := bounded 0 uint_max.

Lemma bounded_range {lo hi : Z} (x : bounded lo hi) : lo <= rval x <= hi.
Proof. apply in_range_spec, rwf. Qed.

Lemma bounded_of_Z_none (lo hi z : Z) :
  bounded_of_Z lo hi z = None <-> ~ (lo <= z <= hi).
Proof.
  unfold bounded_of_Z, bounded. rewrite refined_of_none, <- in_range_spec.
  symmetry. apply not_true_iff_false.
Qed.

(** The bounds of [int] and [uint]. One past either end of [int] is out
    of range, and so is [-1] as a [uint]. *)
Example integer_examples :
  option_map rval (bounded_of_Z int_min int_max int_max) = Some int_max
  /\ bounded_of_Z int_min int_max (int_max + 1) = None
  /\ bounded_of_Z int_min int_max (int_min - 1) = None
  /\ option_map rval (bounded_of_Z 0 uint_max uint_max) = Some uint_max
  /\ bounded_of_Z 0 uint_max (-1) = None.
Proof. repeat split. Qed.

End Integers.

(** ** String characters

    A [string-ascii] value is a sequence of bytes from the [string-ascii]
    character set, and a [string-utf8] value a sequence of Unicode scalar
    values ([Syntax.Lexical], spec 2.2). Both are lists of characters,
    each a refinement by its set: of [Byte.byte] for [string-ascii], as
    for buffers, and of [N] for [string-utf8], whose code points go up to
    U+10FFFF. So a substring, a concatenation or a filtered string needs
    no new proof. The length of the list is what the type's bound counts:
    bytes for [string-ascii], code points for [string-utf8] (2.3.1). A
    [string-utf8] value is encoded in UTF-8 only at the chain ABI
    ([Host.Abi]). *)

Definition is_ascii_byte (b : Byte.byte) : bool :=
  in_ascii_charset (Byte.to_N b).

Definition ascii_char : Type := refined is_ascii_byte.
Definition code_point : Type := refined is_scalar_value.

Definition ascii_string : Type := list ascii_char.
Definition utf8_string : Type := list code_point.

(** The [\u{E9}] of [u"caf\u{E9}"] is a character; a surrogate is not,
    and neither is the byte DEL in a [string-ascii]. *)
Example string_examples :
  option_map rval (refined_of is_scalar_value 0xE9%N) = Some 0xE9%N
  /\ refined_of is_scalar_value 0xD800%N = None
  /\ option_map rval (refined_of is_ascii_byte Byte.x41) = Some Byte.x41
  /\ refined_of is_ascii_byte Byte.x7f = None.
Proof. repeat split. Qed.
