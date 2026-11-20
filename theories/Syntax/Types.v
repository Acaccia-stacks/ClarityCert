(** * Types

    The type grammar, including [never] (spec 2.3.3) and the internal
    contract-literal type, sequence types and element types (2.3.1), the
    storable / interface type predicates (2.3.4), type and size variables
    and static constants as sizes (2.3.5), aliases (2.3.6), and static
    reference kinds, including [(event T)] (2.3.7). *)

From ClarityCert Require Import
  Common.Base
  Common.Limits
  Syntax.Principals.

From Stdlib Require Import OrderedTypeEx.

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
    the type encoding (value layer, section 4.2).

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

    The type checker compares types, so equality on them is decidable.
    [decide equality] gets stuck on [ty], because it has no induction
    hypothesis for the field types of a tuple. So equality on [ty] is
    first a boolean function, [ty_eqb], proved correct with [ty_ind], and
    [ty_eq_dec] is built from it. [ty_eqb] is also what executable code
    such as the type checker can call. *)

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

(** ** Sequence types and element types

    [(buff N)], [(string-ascii N)], [(string-utf8 N)] and [(list N T)] are
    the sequence types. Their element types are [(buff 1)],
    [(string-ascii 1)], [(string-utf8 1)] and [T] (spec 2.3.1): an
    element of a string is a one-character string, a code point for
    [string-utf8].

    The primitive signatures quantify over a sequence kind [S], write
    [S[N]] for that kind with bound [N] and [elem(S)] for its element type
    (spec 3.3). A kind is a sequence type without its bound, so the list
    kind keeps its element type: [(list N T)] is [KList T] with bound [N].
    [seq_ty] and [as_seq] go between the two views. *)

Inductive seq_kind :=
| KBuff
| KAscii
| KUtf8
| KList (t : ty).

Lemma seq_kind_eq_dec (k l : seq_kind) : {k = l} + {k <> l}.
Proof. decide equality; apply ty_eq_dec. Defined.

(** [S[N]]. *)
Definition seq_ty (k : seq_kind) (n : size) : ty :=
  match k with
  | KBuff => TBuff n
  | KAscii => TAscii n
  | KUtf8 => TUtf8 n
  | KList t => TList n t
  end.

(** [elem(S)]. *)
Definition elem_ty (k : seq_kind) : ty :=
  match k with
  | KBuff => TBuff (SLit 1)
  | KAscii => TAscii (SLit 1)
  | KUtf8 => TUtf8 (SLit 1)
  | KList t => t
  end.

(** The kind and bound of a sequence type; [None] for any other type. *)
Definition as_seq (t : ty) : option (seq_kind * size) :=
  match t with
  | TBuff n => Some (KBuff, n)
  | TAscii n => Some (KAscii, n)
  | TUtf8 n => Some (KUtf8, n)
  | TList n u => Some (KList u, n)
  | _ => None
  end.

Definition is_sequence (t : ty) : bool :=
  match as_seq t with
  | Some _ => true
  | None => false
  end.

Lemma as_seq_seq_ty (k : seq_kind) (n : size) :
  as_seq (seq_ty k n) = Some (k, n).
Proof. now destruct k. Qed.

Lemma as_seq_some (t : ty) (k : seq_kind) (n : size) :
  as_seq t = Some (k, n) -> t = seq_ty k n.
Proof. destruct t; simpl; intros H; try discriminate; now inversion H. Qed.

Lemma is_sequence_iff (t : ty) :
  is_sequence t = true <-> exists k n, t = seq_ty k n.
Proof.
  unfold is_sequence. split.
  - destruct (as_seq t) as [[k n] |] eqn:E; [| discriminate].
    intros _. exists k, n. now apply as_seq_some.
  - intros (k & n & ->). now rewrite as_seq_seq_ty.
Qed.

(** The listings type is a list of tuples; a [(string-utf8 20)] has
    elements of type [(string-utf8 1)]; [int] is not a sequence. *)
Example sequence_examples :
  as_seq example_listings_type
    = Some (KList (TTuple [("id"%string, TUInt); ("price"%string, TUInt);
                           ("seller"%string, TPrincipal)]), SLit 10)
  /\ option_map (fun p => elem_ty (fst p)) (as_seq (TUtf8 (SLit 20)))
       = Some (TUtf8 (SLit 1))
  /\ is_sequence TInt = false.
Proof. repeat split. Qed.

(** ** Structural predicates

    Later rules ask what a type contains, at any depth:
    - a type or size variable ([has_var]): storable and interface types
      have none (2.3.4), and neither do the types of public and
      read-only functions, storage or constants (2.3.5);
    - a trait type ([has_trait]): storable types have none (2.3.4);
    - the internal contract-literal type ([has_contract]): it is never an
      interface or storable type (2.3.1).
    All three are instances of [ty_existsb p q t]: some type inside [t],
    [t] included, satisfies [p], or some size inside [t] satisfies [q].

    [sorted_tuples t] holds when the fields of every tuple in [t] are in
    strictly ascending byte order of name. The spec has no such
    predicate: it is how the formalization represents a tuple type. A
    tuple type denotes "records with exactly the listed fields" whose
    names "MUST be distinct" (2.3.1), so the order in which source lists
    them does not matter, and elaboration sorts them and rejects a
    repeated name (5.4, C15). Keeping every type sorted makes two types
    with the same fields the same term, so types compare structurally.
    The order is the one of the type encoding (value layer, section 4.2)
    and of tuple values on the wire (section 3). Since it is strict, the
    names are distinct: [fields_sorted_nodup]. *)

Fixpoint ty_existsb (p : ty -> bool) (q : size -> bool) (t : ty) : bool :=
  p t
  || match t with
     | TBuff n | TAscii n | TUtf8 n => q n
     | TList n u => q n || ty_existsb p q u
     | TOptional u => ty_existsb p q u
     | TResponse u e => ty_existsb p q u || ty_existsb p q e
     | TTuple fields => existsb (fun f => ty_existsb p q (snd f)) fields
     | _ => false
     end.

Definition has_var (t : ty) : bool :=
  ty_existsb
    (fun u => match u with TVar _ => true | _ => false end)
    (fun n => match n with SVar _ => true | SLit _ => false end)
    t.

Definition has_trait (t : ty) : bool :=
  ty_existsb
    (fun u => match u with TTrait _ => true | _ => false end)
    (fun _ => false)
    t.

Definition has_contract (t : ty) : bool :=
  ty_existsb
    (fun u => match u with TContract _ => true | _ => false end)
    (fun _ => false)
    t.

(** Strictly ascending: each name is below the next. [String.ltb]
    compares byte by byte, a proper prefix first. [names_sorted] and its
    lemmas are local to this file: elsewhere, use [fields_sorted] and
    [fields_sorted_nodup]. *)
#[local] Fixpoint names_sorted (xs : list string) : bool :=
  match xs with
  | x :: (y :: _) as rest => String.ltb x y && names_sorted rest
  | _ => true
  end.

Definition fields_sorted (fields : list (string * ty)) : bool :=
  names_sorted (map fst fields).

Definition sorted_tuples (t : ty) : bool :=
  negb
    (ty_existsb
       (fun u => match u with TTuple fs => negb (fields_sorted fs) | _ => false end)
       (fun _ => false)
       t).

(** Every name after the first is above it, by transitivity. *)
#[local] Lemma names_sorted_lt (x : string) (xs : list string) :
  names_sorted (x :: xs) = true -> Forall (String_as_OT.lt x) xs.
Proof.
  revert x; induction xs as [| y ys IH]; intros x H; [constructor |].
  simpl in H. apply andb_prop in H as [Hxy Hys].
  assert (Hlt : String_as_OT.lt x y).
  { apply String_as_OT.cmp_lt. unfold String_as_OT.cmp, String.ltb in *.
    now destruct (String.compare x y). }
  constructor; [exact Hlt |].
  (* Each later name is above [y], hence above [x]. *)
  apply (Forall_impl _ (fun z Hyz => String_as_OT.lt_trans _ _ _ Hlt Hyz)).
  now apply IH.
Qed.

#[local] Lemma names_sorted_tail (x : string) (xs : list string) :
  names_sorted (x :: xs) = true -> names_sorted xs = true.
Proof.
  destruct xs as [| y ys]; [reflexivity |].
  simpl. now intros [_ H]%andb_prop.
Qed.

#[local] Lemma names_sorted_nodup (xs : list string) :
  names_sorted xs = true -> NoDup xs.
Proof.
  induction xs as [| x xs IH]; intros H; constructor.
  - (* [x] is below every later name, so not equal to any. *)
    intros Hin. apply names_sorted_lt in H.
    rewrite Forall_forall in H. specialize (H x Hin).
    now apply (String_as_OT.lt_not_eq x x).
  - apply IH. now apply names_sorted_tail in H.
Qed.

Lemma fields_sorted_nodup (fields : list (string * ty)) :
  fields_sorted fields = true -> NoDup (map fst fields).
Proof. apply names_sorted_nodup. Qed.

Lemma sorted_tuples_inv (fields : list (string * ty)) :
  sorted_tuples (TTuple fields) = true ->
  fields_sorted fields = true
  /\ Forall (fun f => sorted_tuples (snd f) = true) fields.
Proof.
  unfold sorted_tuples; simpl. rewrite negb_orb, negb_involutive.
  intros [Hs Hfs]%andb_prop. split; [exact Hs |].
  (* No field type has a bad tuple, or [existsb] would find it. *)
  rewrite Forall_forall. intros f Hf.
  apply negb_true_iff, Bool.not_true_iff_false. intros Hex.
  apply negb_true_iff in Hfs.
  rewrite (proj2 (existsb_exists _ _)) in Hfs; [discriminate | now exists f].
Qed.

(** The listings type has no variable and its tuple is sorted. A size
    variable is a variable. [{ b: int, a: int }] is not sorted; nor is a
    tuple with a repeated name, nested in an optional. *)
Example structural_examples :
  has_var example_listings_type = false
  /\ sorted_tuples example_listings_type = true
  /\ has_var (TList (SVar "N") TInt) = true
  /\ sorted_tuples (TTuple [("b"%string, TInt); ("a"%string, TInt)]) = false
  /\ sorted_tuples
       (TOptional (TTuple [("a"%string, TInt); ("a"%string, TBool)])) = false.
Proof. repeat split. Qed.

(** ** Storable types and interface types

    A type is storable if it contains no trait type and no type or size
    variable; only storable types appear in storage definitions and in
    [from-consensus-buff?] (spec 2.3.4). A type is an interface type if
    it contains no type or size variable; trait types are allowed. Only
    interface types appear in the parameters and results of public and
    read-only functions, in trait definitions and in event definitions
    (2.3.4).

    Neither may contain the internal contract-literal type, which "is
    never an interface or storable type" (2.3.1). Both may contain
    [never] (2.3.3).

    Every storable type is an interface type ([storable_interface]): the
    two differ only on traits. *)

Definition interface (t : ty) : bool :=
  negb (has_var t) && negb (has_contract t).

Definition storable (t : ty) : bool :=
  interface t && negb (has_trait t).

Lemma storable_interface (t : ty) :
  storable t = true -> interface t = true.
Proof. unfold storable. now intros [H _]%andb_prop. Qed.

(** The registry of 2.3.4 stores principals, not trait values:
    [principal] is storable, [(trait extension)] is an interface type
    but not storable, and [(list N int)], with a size variable, is
    neither. [(response bool never)], the result type of a public
    function that cannot fail, is both. *)
Example storable_examples :
  storable TPrincipal = true
  /\ interface (TTrait example_trait) = true
  /\ storable (TTrait example_trait) = false
  /\ interface (TList (SVar "N") TInt) = false
  /\ storable (TResponse TBool TNever) = true.
Proof. repeat split. Qed.

(** ** Static reference kinds

    A parameter of a [define-private] or [define-macro] may refer
    statically to a definition of the current contract instead of
    holding a value: a data variable, a map, a fungible or non-fungible
    token, an event, or a function (spec 2.3.7). Its reference kind
    gives the shape of the definition it accepts. Reference kinds are not
    types: they cannot appear in [let] bindings, storage, interfaces,
    tuples or sequences, so they are a separate inductive, and a
    parameter has a type or a reference kind ([param_ty]).

    How an argument's types must relate to the kind's (identical for
    [var], [map] and [non-fungible-token], a supertype for [event], the
    rule of 2.6.2 for [function]) is part of instantiation, in
    [Typing.Instantiation]. A type or size variable may occur in a
    reference kind (2.3.5); [ref_kind_tys] lists the types a kind
    mentions. *)

Inductive ref_kind :=
| RVar (t : ty)
| RMap (k v : ty)
| RFungibleToken
| RNonFungibleToken (t : ty)
| REvent (t : ty)
| RFunction (params : list ty) (result : ty).

Inductive param_ty :=
| PTy (t : ty)
| PRef (r : ref_kind).

Lemma ref_kind_eq_dec (r s : ref_kind) : {r = s} + {r <> s}.
Proof.
  decide equality;
    solve [apply ty_eq_dec | apply (list_eq_dec ty_eq_dec)].
Defined.

Lemma param_ty_eq_dec (p q : param_ty) : {p = q} + {p <> q}.
Proof. decide equality; [apply ty_eq_dec | apply ref_kind_eq_dec]. Defined.

Definition ref_kind_tys (r : ref_kind) : list ty :=
  match r with
  | RVar t | RNonFungibleToken t | REvent t => [t]
  | RMap k v => [k; v]
  | RFungibleToken => []
  | RFunction params result => params ++ [result]
  end.

(** The registry map of 2.3.4 as a reference, [(map uint principal)];
    the event parameter of the overload example of 2.6.2,
    [(event (buff 4))]; and a generic predicate on elements,
    [(function (T) bool)], whose type variable [has_var] finds. *)
Example ref_kind_examples :
  ref_kind_tys (RMap TUInt TPrincipal) = [TUInt; TPrincipal]
  /\ ref_kind_tys (REvent (TBuff (SLit 4))) = [TBuff (SLit 4)]
  /\ existsb has_var (ref_kind_tys (RFunction [TVar "T"] TBool)) = true.
Proof. repeat split. Qed.
