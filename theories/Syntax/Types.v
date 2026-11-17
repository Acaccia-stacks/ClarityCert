(** * Types

    The type grammar, including [never] (spec 2.3.3) and the internal
    contract-literal type, sequence types and element types (2.3.1), the
    storable / interface type predicates (2.3.4), type and size variables
    and static constants as sizes (2.3.5), aliases (2.3.6), and static
    reference kinds, including [(event T)] (2.3.7). *)

From ClarityVerif Require Import
  Common.Base
  Common.Limits
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
    local trait name, is resolved during elaboration. *)

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

(** ** Sizes

    A size bounds the length of a sequence type: [(buff N)],
    [(string-ascii N)], [(string-utf8 N)] and [(list N T)]. In a type it
    is written as a numeral or a name (spec 2.3.1). A name is either a
    static constant, replaced by its value during elaboration, or a size
    variable (2.3.5), which an instantiation maps to a natural number
    (2.6.2). So after elaboration a size is a literal or a size variable.

    This is the size inside a type only. A size passed as an argument,
    which may also be a bare [int] literal rejected later by the type
    checker (spec 5.4, C11), is in [Syntax.Ast]. Size arithmetic, such as
    the [2N + 1] of a primitive's signature, is in
    [Primitives.Signatures]. *)

Inductive size :=
| SLit (n : N)
| SVar (x : string).

Lemma size_eq_dec (s t : size) : {s = t} + {s <> t}.
Proof. decide equality; [apply N.eq_dec | apply string_dec]. Defined.

(** ** Types

    The types of spec 2.3.1, after elaboration:
    - [define-type] aliases are expanded (2.3.6), so no alias remains;
    - a name in type position that is not an alias is a type variable
      ([TVar], 2.3.5); a trait name there is a static error (5.4, C10),
      and a trait type is written [(trait X)] ([TTrait]);
    - [never] is the empty type (2.3.3);
    - [TContract] is the internal contract-literal type: the type of the
      one contract principal named by a literal or a static constant. It
      cannot be written in source (2.3.1).

    A tuple type lists its fields as (name, type) pairs. A field name is
    any identifier, keywords included (2.5.1). The fields of a well-formed
    tuple type are distinct and in ascending byte order of name, as in
    the canonical encoding (value layer, section 3).

    A plain [string] is enough for field names, without proofs as in
    the principal records:
    - a name that is not an identifier is a parse error (chapter 5), so
      it never reaches [ty]; that is a theorem about the lexer, not a
      rule [ty] has to enforce;
    - two fields with the same name are a static error (5.4, C15), so
      [ty] must be able to represent them for the type checker to
      reject them;
    - a proof inside [TTuple] would have to be carried by [ty_ind],
      the equality decision and every function that builds a type.
    Distinct, sorted names are a predicate on types, stated in a later
    section. *)

Local Unset Elimination Schemes.

Inductive ty :=
| TInt
| TUInt
| TBool
| TPrincipal
| TNever
| TBuff (n : size)
| TAscii (n : size)
| TUtf8 (n : size)
| TList (n : size) (t : ty)
| TOptional (t : ty)
| TResponse (t e : ty)
| TTuple (fields : list (string * ty))
| TTrait (x : trait_id)
| TContract (c : contract_id)
| TVar (x : string).

Local Set Elimination Schemes.

(** The induction principle Rocq would generate for [ty] has no
    hypothesis for the types inside a tuple, because they sit in a list.
    So generation is turned off around [ty], and [ty_ind] is written here
    instead: a property holds of a tuple type if it holds of every field
    type, stated with [Forall] so that its Stdlib lemmas
    ([Forall_forall], [Forall_impl]) apply. It is registered as the
    induction scheme of [ty], so a plain [induction t] uses it.

    Turning generation off also drops [ty_rect], [ty_rec] and [ty_sind].
    Nothing needs them: [decide equality] would use [ty_rec], but it gets
    stuck on tuples anyway, so the equality decision on [ty] is written
    by hand. *)

Section TyInd.
  Variable P : ty -> Prop.

  Hypothesis H_int : P TInt.
  Hypothesis H_uint : P TUInt.
  Hypothesis H_bool : P TBool.
  Hypothesis H_principal : P TPrincipal.
  Hypothesis H_never : P TNever.
  Hypothesis H_buff : forall n, P (TBuff n).
  Hypothesis H_ascii : forall n, P (TAscii n).
  Hypothesis H_utf8 : forall n, P (TUtf8 n).
  Hypothesis H_list : forall n t, P t -> P (TList n t).
  Hypothesis H_optional : forall t, P t -> P (TOptional t).
  Hypothesis H_response : forall t e, P t -> P e -> P (TResponse t e).
  Hypothesis H_tuple :
    forall fields, Forall (fun f => P (snd f)) fields -> P (TTuple fields).
  Hypothesis H_trait : forall x, P (TTrait x).
  Hypothesis H_contract : forall c, P (TContract c).
  Hypothesis H_var : forall x, P (TVar x).

  Fixpoint ty_ind (t : ty) : P t :=
    match t with
    | TInt => H_int
    | TUInt => H_uint
    | TBool => H_bool
    | TPrincipal => H_principal
    | TNever => H_never
    | TBuff n => H_buff n
    | TAscii n => H_ascii n
    | TUtf8 n => H_utf8 n
    | TList n u => H_list n u (ty_ind u)
    | TOptional u => H_optional u (ty_ind u)
    | TResponse u e => H_response u e (ty_ind u) (ty_ind e)
    | TTuple fields =>
        H_tuple fields
          ((fix fields_ind (fs : list (string * ty))
              : Forall (fun f => P (snd f)) fs :=
              match fs with
              | [] => Forall_nil _
              | (x, u) :: rest =>
                  Forall_cons (x, u) (ty_ind u) (fields_ind rest)
              end) fields)
    | TTrait x => H_trait x
    | TContract c => H_contract c
    | TVar x => H_var x
    end.
End TyInd.

Register Scheme ty_ind as ind_nodep for ty.

(** The data type of the [listed] event of spec 3.10, in a list:
    [(list 10 { id: uint, price: uint, seller: principal })]. *)
Example example_listings_type : ty :=
  TList (SLit 10)
    (TTuple [("id"%string, TUInt); ("price"%string, TUInt); ("seller"%string, TPrincipal)]).
