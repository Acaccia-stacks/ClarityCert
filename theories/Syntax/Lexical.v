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
