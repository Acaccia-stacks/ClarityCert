(** * Principals

    Standard and contract principals, contract identifiers and trait
    identifiers (chain ABI 2.1-2.2; spec 2.2), with their well-formedness
    rules built in, and decidable equality on each. *)

From ClarityCert Require Import
  Common.Base
  Syntax.Lexical.

From Stdlib Require Import Eqdep_dec.

(** ** Principals and identifiers

    A standard principal is a version byte and a 20-byte hash; a contract
    principal adds a contract name (chain ABI 2.2). A trait is named by
    its defining contract and its name (value layer, section 2).

    Every principal value has a version below 32, a 20-byte hash and a
    valid contract name, whether it comes from a literal, is built at
    runtime or is decoded: decoding accepts exactly this form (chain ABI
    2.2). The records carry these rules as boolean proofs, so invalid
    principals cannot be represented, and two principals are equal when
    their parts are ([standard_principal_ext], [contract_id_ext]). A trait
    name is not constrained: one that is not a vNEXT identifier can still
    appear in [abi.types] (spec 5.6).

    Identifiers here are resolved: a deployer-relative [.name], or a bare
    local trait name, is resolved during elaboration.

    Types name contracts and traits ([TContract], [TTrait] in
    [Syntax.Types]) and values hold principals ([Syntax.Values]), so
    both import this module. *)

Record standard_principal := {
  sp_version : Byte.byte;
  sp_hash : list Byte.byte;
  sp_wf :
    N.ltb (Byte.to_N sp_version) 32 && Nat.eqb (length sp_hash) 20 = true;
}.

Record contract_id := {
  ci_issuer : standard_principal;
  ci_name : string;
  ci_wf : valid_contract_name ci_name = true;
}.

Lemma standard_principal_ext (p q : standard_principal) :
  sp_version p = sp_version q -> sp_hash p = sp_hash q -> p = q.
Proof.
  destruct p as [v h wf], q as [v' h' wf']; simpl; intros -> ->.
  f_equal. apply UIP_dec, bool_dec.
Qed.

Lemma contract_id_ext (c d : contract_id) :
  ci_issuer c = ci_issuer d -> ci_name c = ci_name d -> c = d.
Proof.
  destruct c as [i n wf], d as [i' n' wf']; simpl; intros -> ->.
  f_equal. apply UIP_dec, bool_dec.
Qed.

Lemma sp_version_bound (p : standard_principal) :
  (Byte.to_N (sp_version p) < 32)%N.
Proof.
  destruct p as [v h wf]; simpl.
  apply andb_prop in wf as [H _]. now apply N.ltb_lt.
Qed.

Lemma sp_hash_length (p : standard_principal) :
  length (sp_hash p) = 20.
Proof.
  destruct p as [v h wf]; simpl.
  apply andb_prop in wf as [_ H]. now apply Nat.eqb_eq.
Qed.

(** A concrete principal is built with [eq_refl] as its proof; one with
    version 32 or a 19-byte hash does not typecheck. *)
Example example_principal : standard_principal :=
  {| sp_version := Byte.x16; sp_hash := repeat Byte.x00 20; sp_wf := eq_refl |}.

Example example_contract : contract_id :=
  {| ci_issuer := example_principal; ci_name := "counter"; ci_wf := eq_refl |}.

Inductive principal :=
| PStandard (p : standard_principal)
| PContract (c : contract_id).

Record trait_id := {
  ti_contract : contract_id;
  ti_name : string;
}.

(** A trait, for the examples: [extension] of the example contract. *)
Example example_trait : trait_id :=
  {| ti_contract := example_contract; ti_name := "extension" |}.

(** ** Decidable equality

    The semantics compares principals and traits, so equality on them is
    decidable. *)

Lemma standard_principal_eq_dec (p q : standard_principal) :
  {p = q} + {p <> q}.
Proof.
  destruct (Byte.byte_eq_dec (sp_version p) (sp_version q)) as [Hv | Hv];
    [destruct (list_eq_dec Byte.byte_eq_dec (sp_hash p) (sp_hash q))
       as [Hh | Hh] |].
  - left. now apply standard_principal_ext.
  - right. intros ->. now apply Hh.
  - right. intros ->. now apply Hv.
Defined.

Lemma contract_id_eq_dec (c d : contract_id) : {c = d} + {c <> d}.
Proof.
  destruct (standard_principal_eq_dec (ci_issuer c) (ci_issuer d))
    as [Hi | Hi];
    [destruct (string_dec (ci_name c) (ci_name d)) as [Hn | Hn] |].
  - left. now apply contract_id_ext.
  - right. intros ->. now apply Hn.
  - right. intros ->. now apply Hi.
Defined.

Lemma principal_eq_dec (p q : principal) : {p = q} + {p <> q}.
Proof.
  decide equality; [apply standard_principal_eq_dec | apply contract_id_eq_dec].
Defined.

Lemma trait_id_eq_dec (x y : trait_id) : {x = y} + {x <> y}.
Proof. decide equality; [apply string_dec | apply contract_id_eq_dec]. Defined.
