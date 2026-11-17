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

(** ** Decidable equality

    The type checker compares types, and the semantics compares
    principals and traits, so equality is decidable on all of them. Each
    decision ends with [Defined] rather than [Qed] so that it computes
    inside Rocq: an [if ty_eq_dec s t then ... else ...] reduces to one
    of its branches, as [Example]s, conformance vectors and proofs by
    computation need. The proof carried by [left] or [right] can use
    opaque lemmas such as [standard_principal_ext]: computation only
    needs to reach [left] or [right].

    [decide equality] gets stuck on [ty], because it has no induction
    hypothesis for the field types of a tuple. So equality on [ty] is
    first a boolean function, [ty_eqb], proved correct with [ty_ind], and
    [ty_eq_dec] is built from it. [ty_eqb] is also what executable code
    such as the type checker can call. *)

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

Fixpoint ty_eqb (s t : ty) : bool :=
  match s, t with
  | TInt, TInt | TUInt, TUInt | TBool, TBool
  | TPrincipal, TPrincipal | TNever, TNever => true
  | TBuff n, TBuff m | TAscii n, TAscii m | TUtf8 n, TUtf8 m =>
      if size_eq_dec n m then true else false
  | TList n u, TList m v =>
      if size_eq_dec n m then ty_eqb u v else false
  | TOptional u, TOptional v => ty_eqb u v
  | TResponse u e, TResponse v f => ty_eqb u v && ty_eqb e f
  | TTuple fs, TTuple gs =>
      (fix fields_eqb (fs gs : list (string * ty)) : bool :=
         match fs, gs with
         | [], [] => true
         | (x, u) :: fs', (y, v) :: gs' =>
             String.eqb x y && ty_eqb u v && fields_eqb fs' gs'
         | _, _ => false
         end) fs gs
  | TTrait x, TTrait y => if trait_id_eq_dec x y then true else false
  | TContract c, TContract d => if contract_id_eq_dec c d then true else false
  | TVar x, TVar y => String.eqb x y
  | _, _ => false
  end.

Lemma ty_eqb_true (s t : ty) : ty_eqb s t = true -> s = t.
Proof.
  (* Induction on [s] for every [t]: inner types are compared with other
     types than [t]. Then split [t]; mismatched constructors give
     [false = true]. *)
  revert t; induction s; intros [] Heq; simpl in Heq; try discriminate;
    (* Break the test into one fact per argument. *)
    repeat match goal with
      | H : _ && _ = true |- _ => apply andb_prop in H as [? ?]
      (* A decision on sizes, traits or contracts: its [right] case gives
         [false = true]. *)
      | H : (if ?d then _ else false) = true |- _ =>
          destruct d; [| discriminate]
      | H : String.eqb _ _ = true |- _ => apply String.eqb_eq in H
      (* An inner type: the induction hypothesis makes it equal. *)
      | IH : forall t, ty_eqb ?u t = true -> ?u = t,
        H : ty_eqb ?u _ = true |- _ => apply IH in H
      end;
    (* Every argument is equal, so the two types are. *)
    subst; try reflexivity.
  (* Tuples are left: walk both field lists together, with the induction
     hypothesis for each field type from [Forall]. *)
  revert fields0 Heq.
  induction H as [| [x u] fs Hu _ IH]; intros [| [y v] gs] Heq;
    (* Both empty, or lists of different lengths. *)
    simpl in *; try discriminate; [reflexivity |].
  (* Same name, same field type, and the rest by [IH]. *)
  apply andb_prop in Heq as [Heq Hgs]. apply andb_prop in Heq as [Hx Huv].
  apply String.eqb_eq in Hx as ->. apply Hu in Huv as ->.
  specialize (IH gs Hgs). congruence.
Qed.

Lemma ty_eqb_refl (t : ty) : ty_eqb t t = true.
Proof.
  (* Compare each type with itself, constructor by constructor. *)
  induction t; simpl;
    (* A decision on two equal sizes, traits or contracts: its [right]
       case claims [x <> x], a contradiction. *)
    repeat match goal with
      | |- context [if ?d then _ else false] =>
          destruct d; [| congruence]
      end;
    (* Equal names compare [true]; an inner type does by induction. *)
    rewrite ?String.eqb_refl, ?andb_true_r; auto.
  (* Responses: both inner types, by induction. *)
  - now rewrite IHt1, IHt2.
  (* Tuples: walk the field list, with the induction hypothesis for each
     field type from [Forall]. *)
  - induction H as [| [x u] fs Hu _ IH]; simpl in *; [reflexivity |].
    now rewrite String.eqb_refl, Hu, IH.
Qed.

Lemma ty_eqb_eq (s t : ty) : ty_eqb s t = true <-> s = t.
Proof. split; [apply ty_eqb_true | intros ->; apply ty_eqb_refl]. Qed.

Lemma ty_eq_dec (s t : ty) : {s = t} + {s <> t}.
Proof.
  destruct (ty_eqb s t) eqn:E; [left | right].
  - now apply ty_eqb_eq.
  - intros H. apply ty_eqb_eq in H. congruence.
Defined.

Example ty_eq_dec_computes :
  (if ty_eq_dec example_listings_type example_listings_type then 1 else 2) = 1
  /\ (if ty_eq_dec (TOptional TInt) (TOptional TUInt) then 1 else 2) = 2.
Proof. split; reflexivity. Qed.
