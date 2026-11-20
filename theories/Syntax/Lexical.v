(** * Lexical structure

    Well-formedness of identifiers, literals (including the [string-ascii]
    character set and the one spelling of each [\u{H}] escape), principal
    literals and contract names; keywords and reserved names (spec 2.2).
    These are the token rules of the grammar's Part L, the character set
    (T3) and the lexical checks LX1-LX7 (chapter 5), stated as predicates
    for the lexer to be proved against. *)

From ClarityCert Require Import
  Common.Base
  Common.Limits.

From Stdlib Require Import Ascii.

(** ** Contract names

    A contract name is 1 to 40 characters: an ASCII letter, then letters,
    digits, [-] or [_] (spec 2.2, chain ABI 2.1). The same rule applies
    wherever a contract name appears, in literals, at runtime and on the
    wire, so it is also an invariant of principal values ([Syntax.Types]).
    Stated as a boolean so that it can be carried as a proof of
    [valid_contract_name s = true]. *)

Definition max_contract_name_length : nat := 40.

Definition is_ascii_letter (c : Ascii.ascii) : bool :=
  let n := Ascii.N_of_ascii c in
  (((65 <=? n) && (n <=? 90)) || ((97 <=? n) && (n <=? 122)))%N.

Definition is_ascii_digit (c : Ascii.ascii) : bool :=
  let n := Ascii.N_of_ascii c in
  ((48 <=? n) && (n <=? 57))%N.

Definition is_contract_name_char (c : Ascii.ascii) : bool :=
  is_ascii_letter c || is_ascii_digit c
  || Ascii.eqb c "-"%char || Ascii.eqb c "_"%char.

Definition valid_contract_name (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c rest =>
      is_ascii_letter c
      && forallb is_contract_name_char (list_ascii_of_string rest)
      && Nat.leb (String.length s) max_contract_name_length
  end.

Lemma valid_contract_name_length (s : string) :
  valid_contract_name s = true ->
  1 <= String.length s <= max_contract_name_length.
Proof.
  destruct s as [| c rest]; simpl; [discriminate |].
  intros H. apply andb_prop in H as [_ H].
  apply Nat.leb_le in H. unfold max_contract_name_length. lia.
Qed.

Example valid_contract_name_examples :
  valid_contract_name "counter" = true /\
  valid_contract_name "a-b_9" = true /\
  valid_contract_name "9a" = false /\
  valid_contract_name "-a" = false /\
  valid_contract_name "a.b" = false /\
  valid_contract_name "" = false /\
  (* 40 characters, then 41 *)
  valid_contract_name
    ("aaaaaaaaaa" ++ "aaaaaaaaaa" ++ "aaaaaaaaaa" ++ "aaaaaaaaaa") = true /\
  valid_contract_name
    ("aaaaaaaaaa" ++ "aaaaaaaaaa" ++ "aaaaaaaaaa" ++ "aaaaaaaaaa" ++ "a")
    = false.
Proof. repeat split; reflexivity. Qed.

(** ** Character sets

    The [string-ascii] character set is the printable ASCII characters
    0x20 to 0x7E, plus tab (0x09), line feed (0x0A) and carriage return
    (0x0D); no [string-ascii] value ever holds another byte (spec 2.2).
    A [string-utf8] value is a sequence of Unicode scalar values: the
    code points up to U+10FFFF, except the surrogates U+D800 to U+DFFF
    (2.2, LX5; value layer, section 3). U+0000 is one.

    Both are stated on [N], for bytes and code points alike. *)

Definition in_ascii_charset (n : N) : bool :=
  ((0x20 <=? n) && (n <=? 0x7E)
   || (n =? 0x09) || (n =? 0x0A) || (n =? 0x0D))%N.

Definition is_scalar_value (n : N) : bool :=
  ((n <=? 0x10FFFF) && negb ((0xD800 <=? n) && (n <=? 0xDFFF)))%N.

(** Space, tilde and tab are in the [string-ascii] set; DEL (0x7F) and
    NUL are not. U+0000, U+E9 and U+10FFFF are scalar values; a
    surrogate and U+110000 are not. *)
Example character_set_examples :
  in_ascii_charset 0x20 = true /\ in_ascii_charset 0x7E = true
  /\ in_ascii_charset 0x09 = true /\ in_ascii_charset 0x7F = false
  /\ in_ascii_charset 0x00 = false
  /\ is_scalar_value 0x0 = true /\ is_scalar_value 0xE9 = true
  /\ is_scalar_value 0x10FFFF = true /\ is_scalar_value 0xD800 = false
  /\ is_scalar_value 0x110000 = false.
Proof. repeat split. Qed.
