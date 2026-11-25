(** * Abstract syntax

    Surface syntax of contracts, following Part S of the grammar (spec
    chapter 5): the version declaration (2.4.0), definition forms,
    including [define-event] (2.4.1), top-level expressions (2.4.2),
    expression forms, including [contract-call-raw?], and allowances
    (2.5), the dedicated forms of [map] and of the primitives that take a
    type or size (3.3, 3.4), rest parameters and spread arguments (2.6.5).
    It keeps what the grammar accepts and the type checker rejects (5.4),
    such as a bare [int] literal as a size argument. *)

From ClarityCert Require Import
  Common.Base
  Syntax.Lexical
  Syntax.Principals
  Syntax.Types
  Syntax.Values.

(** ** Source types

    Types as written in source (grammar S.4, S.5), before elaboration
    turns them into [ty] (spec 2.3.1, 2.3.5, 2.3.6):
    - a bare name in type position ([SrcName]) is an alias, a type
      variable or a misplaced trait name (C10, 5.4); only elaboration can
      tell, so it stays a name here;
    - a size ([src_size]) is a numeral or a name, which is a static
      constant or a size variable; [(buff u32)] is a parse error, so a
      numeral is a natural number;
    - a contract or trait may be named relative to the deployer, [.c] or
      [.c.t], or locally by a bare trait name;
    - a tuple type keeps its fields in source order, repeated names
      included (C15).
    The internal contract-literal type cannot be written, so it has no
    source form. Reference kinds have the same shape as after
    elaboration, over source types: [ref_kind src_ty].

    Identifiers are strings: their spelling (LX rules, 5.3) is checked
    by the lexer and stated in [Syntax.Lexical]. A principal literal is
    already decoded by the lexer (LX4), so it is a [standard_principal],
    and a contract name carries its validity. *)

(** A contract named in source: in full, or relative to the deployer
    ([.c]). *)
Inductive src_contract :=
| ContractAbs (c : contract_id)
| ContractRel (name : refined valid_contract_name).

(** A trait named in source: [c.t] with [c] a contract, or a bare name
    for a trait of this contract. *)
Inductive src_trait :=
| TraitLit (c : src_contract) (name : string)
| TraitName (x : string).

Inductive src_size :=
| SizeLit (n : N)
| SizeName (x : string).

Local Unset Elimination Schemes.

Inductive src_ty :=
| SrcInt
| SrcUInt
| SrcBool
| SrcPrincipal
| SrcNever
| SrcBuff (n : src_size)
| SrcAscii (n : src_size)
| SrcUtf8 (n : src_size)
| SrcList (n : src_size) (t : src_ty)
| SrcOptional (t : src_ty)
| SrcResponse (t e : src_ty)
| SrcTuple (fields : list (string * src_ty))
| SrcTrait (x : src_trait)
| SrcName (x : string).

Local Set Elimination Schemes.

Section SrcTyInd.
  Variable P : src_ty -> Prop.

  Hypothesis H_int : P SrcInt.
  Hypothesis H_uint : P SrcUInt.
  Hypothesis H_bool : P SrcBool.
  Hypothesis H_principal : P SrcPrincipal.
  Hypothesis H_never : P SrcNever.
  Hypothesis H_buff : forall n, P (SrcBuff n).
  Hypothesis H_ascii : forall n, P (SrcAscii n).
  Hypothesis H_utf8 : forall n, P (SrcUtf8 n).
  Hypothesis H_list : forall n t, P t -> P (SrcList n t).
  Hypothesis H_optional : forall t, P t -> P (SrcOptional t).
  Hypothesis H_response : forall t e, P t -> P e -> P (SrcResponse t e).
  Hypothesis H_tuple :
    forall fields, Forall (fun f => P (snd f)) fields -> P (SrcTuple fields).
  Hypothesis H_trait : forall x, P (SrcTrait x).
  Hypothesis H_name : forall x, P (SrcName x).

  Fixpoint src_ty_ind (t : src_ty) : P t :=
    match t with
    | SrcInt => H_int
    | SrcUInt => H_uint
    | SrcBool => H_bool
    | SrcPrincipal => H_principal
    | SrcNever => H_never
    | SrcBuff n => H_buff n
    | SrcAscii n => H_ascii n
    | SrcUtf8 n => H_utf8 n
    | SrcList n u => H_list n u (src_ty_ind u)
    | SrcOptional u => H_optional u (src_ty_ind u)
    | SrcResponse u e => H_response u e (src_ty_ind u) (src_ty_ind e)
    | SrcTuple fields =>
        H_tuple fields
          ((fix fields_ind (fs : list (string * src_ty))
              : Forall (fun f => P (snd f)) fs :=
              match fs with
              | [] => Forall_nil _
              | (x, u) :: rest =>
                  Forall_cons (x, u) (src_ty_ind u) (fields_ind rest)
              end) fields)
    | SrcTrait x => H_trait x
    | SrcName x => H_name x
    end.
End SrcTyInd.

Register Scheme src_ty_ind as ind_nodep for src_ty.

(** The listings type of 3.10 as written, with its bound a static
    constant [MAX-LISTINGS]; the reference to a map of listings by id;
    and [(trait .registry.extension)], relative to the deployer. *)
Example example_src_listings : src_ty :=
  SrcList (SizeName "MAX-LISTINGS")
    (SrcTuple [("id"%string, SrcUInt); ("price"%string, SrcUInt);
               ("seller"%string, SrcPrincipal)]).

Example example_src_ref : ref_kind src_ty :=
  RMap SrcUInt (SrcName "listing").

Example example_src_trait : src_ty :=
  SrcTrait
    (TraitLit
       (ContractRel {| rval := "registry"%string; rwf := eq_refl |})
       "extension").

(** ** Literals

    The literals of an expression (grammar S.3, spec 2.2). The lexer
    decodes each token into what it denotes, so a literal holds a value
    of the matching kind, with the parse errors of 5.3 already ruled out
    by the representation:
    - an integer is in range: LX1 and LX6 for [int], LX3 for [uint]. A
      numeral in expression position is an [int] (LX6), also where a
      size term is expected (C11);
    - a string holds its characters, escapes decoded: [string-ascii]
      bytes, or [string-utf8] scalar values (LX5);
    - a standard principal is decoded from c32check (LX4);
    - a buffer is its bytes.
    A contract principal may be relative to the deployer ([.c]), so it
    is a [src_contract]; its value is fixed during elaboration, once the
    deployer is known ([Typing.Elaborate]). A trait identifier is not a literal: it appears
    only in types and trait references. *)

Inductive literal :=
| LInt (i : int128)
| LUInt (u : uint128)
| LBool (b : bool)
| LBuff (bs : list Byte.byte)
| LAscii (s : ascii_string)
| LUtf8 (s : utf8_string)
| LPrincipal (p : standard_principal)
| LContract (c : src_contract)
| LNone.

(** [.counter], a contract relative to the deployer (2.2). *)
Example example_contract_literal : literal :=
  LContract (ContractRel {| rval := "counter"%string; rwf := eq_refl |}).

(** ** Parts of expressions

    The pieces an expression is built from that are not themselves
    expressions (grammar S.7, S.8).

    A size is the number in a type: the [N] of [(buff N)],
    [(string-ascii N)] or [(list N T)] (2.3.1). Five primitives take one
    as an argument because it is the bound of their result type (3.3,
    3.4): [(as-max-len? xs u10)] is an [(optional (list 10 T))], and
    [(uint-to-buff-be n u16)] a [(buff 16)]. Types are static, so the
    argument must be known before the code runs: it is a [size_term], a
    [uint] literal or a name, which is a size variable or a static
    constant, never an expression (a parse error). A bare [int] literal
    there parses and is a static type error (C11), so it has its own
    constructor.

    The calls of these five primitives are dedicated forms, not
    applications (2.5.5), and share one shape: an expression and a size
    term. They are listed by [prim_with_size]. The two other dedicated
    forms, [from-consensus-buff?] and [map], have their own constructors
    in [expr].

    An allowance (2.5.9) holds expressions, and so does a body ([body =
    expr, {expr}], S.6), so both are parametric in their expression
    type, as [ref_kind] is in its type ([Syntax.Types]): [expr] uses
    [allowance expr] and [body expr]. A body has a first expression, so
    an empty body cannot be represented. The order of allowances is kept:
    a violated allowance is reported by its index (2.5.9).
    [(with-all-assets-unsafe)] is accepted only by [as-contract?], as
    its only allowance; the grammar encodes both rules, and so does
    [contract_allowances]. *)

Inductive size_term :=
| SizeTermUInt (u : uint128)
| SizeTermName (x : string)
| SizeTermInt (i : int128).

Inductive prim_with_size :=
| AsMaxLen
| UIntToBuffBE
| UIntToBuffLE
| IntToBuffBE
| IntToBuffLE.

(** The arguments, in order: the [amount] for [with-stx] and
    [with-staking]; the [contract], the [token-name] and the [amount] for
    [with-ft]; the [contract], the [token-name] and the [identifiers] for
    [with-nft]. *)
Inductive allowance (A : Type) :=
| WithStx (amount : A)
| WithFt (contract token amount : A)
| WithNft (contract token ids : A)
| WithStaking (amount : A)
| WithPox.

Arguments WithStx {A}. Arguments WithFt {A}. Arguments WithNft {A}.
Arguments WithStaking {A}. Arguments WithPox {A}.

(** The allowances of [as-contract?]. *)
Inductive contract_allowances (A : Type) :=
| AllAssetsUnsafe
| Allowances (l : list (allowance A)).

Arguments AllAssetsUnsafe {A}. Arguments Allowances {A}.

Inductive body (A : Type) := Body (first : A) (rest : list A).

Arguments Body {A}.

(** The expressions an allowance or a body holds, in evaluation order
    (2.5.9 for allowances). *)
Definition allowance_args {A} (a : allowance A) : list A :=
  match a with
  | WithStx x | WithStaking x => [x]
  | WithFt c t x | WithNft c t x => [c; t; x]
  | WithPox => []
  end.

Definition body_exprs {A} (b : body A) : list A :=
  let 'Body e es := b in e :: es.

(** [(as-max-len? s u4)] passes a size term [u4]; in
    [(as-max-len? s 4)], the [4] is a bare [int], a static type error
    (3.3). *)
Example size_term_examples : size_term * size_term :=
  (SizeTermUInt {| rval := 4%Z; rwf := eq_refl |},
   SizeTermInt {| rval := 4%Z; rwf := eq_refl |}).

(** ** Expressions

    The expression forms of the grammar (S.7-S.9, spec 2.5), one
    constructor each, with these representation choices:
    - [match] has one constructor per pair of arms (2.5.3): on an
      optional, a response or a [bool]. The grammar accepts each pair in
      either order; the order has no effect, since exactly one arm is
      evaluated and the type is the lub of both, so it is not kept;
    - [and] and [or] take at least two operands, so they hold two
      expressions and a list (2.5.3);
    - a tuple keeps its fields in source order, repeated names included
      (C15), as a tuple type does ([src_ty]);
    - the five primitives with a size argument share [EPrimWithSize];
    - an application holds its arguments and, apart, the spread argument
      [e...], at most one and the last (2.5.5, 2.6.5).
    Bound names, field names and function names are strings; which
    identifiers they may be (a name, or any identifier for a field or a
    foreign function) is checked by the parser (S.2). *)

Local Unset Elimination Schemes.

Inductive expr :=
| ELit (l : literal)
| EName (x : string)
| ELet (bindings : list (string * expr)) (b : body expr)
| EBegin (b : body expr)
| EMatchOptional (e : expr) (x : string) (some_b none_b : body expr)
| EMatchResponse (e : expr) (x : string) (ok_b : body expr)
    (y : string) (err_b : body expr)
| EMatchBool (e : expr) (true_b false_b : body expr)
| EAnd (e1 e2 : expr) (es : list expr)
| EOr (e1 e2 : expr) (es : list expr)
| EReturn (e : expr)
| ESome (e : expr)
| EOk (e : expr)
| EErr (e : expr)
| EList (es : list expr)
| ETuple (fields : list (string * expr))
| EGet (x : string) (e : expr)
| EMerge (e1 e2 : expr)
| EContractCall (target : expr) (f : string) (args : list expr)
| EContractCallRaw (target : expr) (f : string) (arg : expr) (n : size_term)
| EAsContract (allows : contract_allowances expr) (b : body expr)
| ERestrictAssets (owner : expr) (allows : list (allowance expr))
    (b : body expr)
| EAs (t : src_ty) (e : expr)
| EPrimWithSize (p : prim_with_size) (e : expr) (n : size_term)
| EFromConsensusBuff (t : src_ty) (e : expr)
| EMap (f : string) (e : expr)
| EApp (f : string) (args : list expr) (spread : option expr).

Local Set Elimination Schemes.

(** The allowances of [as-contract?] as a list, empty for
    [(with-all-assets-unsafe)]; and the expression an option holds. *)
Definition contract_allowances_list {A} (c : contract_allowances A)
    : list (allowance A) :=
  match c with
  | AllAssetsUnsafe => []
  | Allowances l => l
  end.

Definition option_exprs {A} (o : option A) : list A :=
  match o with
  | Some a => [a]
  | None => []
  end.

(** The induction principle: every sub-expression, inside a list, a
    body, an allowance or an option, has an induction hypothesis, stated
    with [Forall] over the lists above. *)
Section ExprInd.
  Variable P : expr -> Prop.

  Let PBody (b : body expr) := Forall P (body_exprs b).
  Let PFields (fs : list (string * expr)) := Forall (fun f => P (snd f)) fs.
  Let PAllows (l : list (allowance expr)) :=
    Forall (fun a => Forall P (allowance_args a)) l.

  Hypothesis H_lit : forall l, P (ELit l).
  Hypothesis H_name : forall x, P (EName x).
  Hypothesis H_let : forall bs b, PFields bs -> PBody b -> P (ELet bs b).
  Hypothesis H_begin : forall b, PBody b -> P (EBegin b).
  Hypothesis H_match_optional : forall e x sb nb,
    P e -> PBody sb -> PBody nb -> P (EMatchOptional e x sb nb).
  Hypothesis H_match_response : forall e x ob y eb,
    P e -> PBody ob -> PBody eb -> P (EMatchResponse e x ob y eb).
  Hypothesis H_match_bool : forall e tb fb,
    P e -> PBody tb -> PBody fb -> P (EMatchBool e tb fb).
  Hypothesis H_and : forall e1 e2 es,
    P e1 -> P e2 -> Forall P es -> P (EAnd e1 e2 es).
  Hypothesis H_or : forall e1 e2 es,
    P e1 -> P e2 -> Forall P es -> P (EOr e1 e2 es).
  Hypothesis H_return : forall e, P e -> P (EReturn e).
  Hypothesis H_some : forall e, P e -> P (ESome e).
  Hypothesis H_ok : forall e, P e -> P (EOk e).
  Hypothesis H_err : forall e, P e -> P (EErr e).
  Hypothesis H_list : forall es, Forall P es -> P (EList es).
  Hypothesis H_tuple : forall fs, PFields fs -> P (ETuple fs).
  Hypothesis H_get : forall x e, P e -> P (EGet x e).
  Hypothesis H_merge : forall e1 e2, P e1 -> P e2 -> P (EMerge e1 e2).
  Hypothesis H_contract_call : forall t f args,
    P t -> Forall P args -> P (EContractCall t f args).
  Hypothesis H_contract_call_raw : forall t f a n,
    P t -> P a -> P (EContractCallRaw t f a n).
  Hypothesis H_as_contract : forall c b,
    PAllows (contract_allowances_list c) -> PBody b -> P (EAsContract c b).
  Hypothesis H_restrict_assets : forall o l b,
    P o -> PAllows l -> PBody b -> P (ERestrictAssets o l b).
  Hypothesis H_as : forall t e, P e -> P (EAs t e).
  Hypothesis H_prim_with_size : forall p e n, P e -> P (EPrimWithSize p e n).
  Hypothesis H_from_consensus_buff : forall t e,
    P e -> P (EFromConsensusBuff t e).
  Hypothesis H_map : forall f e, P e -> P (EMap f e).
  Hypothesis H_app : forall f args sp,
    Forall P args -> Forall P (option_exprs sp) -> P (EApp f args sp).

  Fixpoint expr_ind (e : expr) : P e :=
    let exprs_ind :=
      fix exprs_ind (es : list expr) : Forall P es :=
        match es with
        | [] => Forall_nil _
        | e' :: rest => Forall_cons e' (expr_ind e') (exprs_ind rest)
        end in
    let body_ind (b : body expr) : PBody b :=
      match b as b' return PBody b' with
      | Body e' es => Forall_cons e' (expr_ind e') (exprs_ind es)
      end in
    let fields_ind :=
      fix fields_ind (fs : list (string * expr)) : PFields fs :=
        match fs with
        | [] => Forall_nil _
        | (x, e') :: rest =>
            Forall_cons (x, e') (expr_ind e') (fields_ind rest)
        end in
    let allowance_ind (a : allowance expr) : Forall P (allowance_args a) :=
      match a as a' return Forall P (allowance_args a') with
      | WithStx x | WithStaking x => Forall_cons x (expr_ind x) (Forall_nil _)
      | WithFt c t x | WithNft c t x =>
          Forall_cons c (expr_ind c)
            (Forall_cons t (expr_ind t)
               (Forall_cons x (expr_ind x) (Forall_nil _)))
      | WithPox => Forall_nil _
      end in
    let allows_ind :=
      fix allows_ind (l : list (allowance expr)) : PAllows l :=
        match l with
        | [] => Forall_nil _
        | a :: rest => Forall_cons a (allowance_ind a) (allows_ind rest)
        end in
    match e with
    | ELit l => H_lit l
    | EName x => H_name x
    | ELet bs b => H_let bs b (fields_ind bs) (body_ind b)
    | EBegin b => H_begin b (body_ind b)
    | EMatchOptional e' x sb nb =>
        H_match_optional e' x sb nb (expr_ind e') (body_ind sb) (body_ind nb)
    | EMatchResponse e' x ob y eb =>
        H_match_response e' x ob y eb (expr_ind e') (body_ind ob) (body_ind eb)
    | EMatchBool e' tb fb =>
        H_match_bool e' tb fb (expr_ind e') (body_ind tb) (body_ind fb)
    | EAnd e1 e2 es => H_and e1 e2 es (expr_ind e1) (expr_ind e2) (exprs_ind es)
    | EOr e1 e2 es => H_or e1 e2 es (expr_ind e1) (expr_ind e2) (exprs_ind es)
    | EReturn e' => H_return e' (expr_ind e')
    | ESome e' => H_some e' (expr_ind e')
    | EOk e' => H_ok e' (expr_ind e')
    | EErr e' => H_err e' (expr_ind e')
    | EList es => H_list es (exprs_ind es)
    | ETuple fs => H_tuple fs (fields_ind fs)
    | EGet x e' => H_get x e' (expr_ind e')
    | EMerge e1 e2 => H_merge e1 e2 (expr_ind e1) (expr_ind e2)
    | EContractCall t f args =>
        H_contract_call t f args (expr_ind t) (exprs_ind args)
    | EContractCallRaw t f a n =>
        H_contract_call_raw t f a n (expr_ind t) (expr_ind a)
    | EAsContract c b =>
        H_as_contract c b
          (match c as c' return PAllows (contract_allowances_list c') with
           | AllAssetsUnsafe => Forall_nil _
           | Allowances l => allows_ind l
           end)
          (body_ind b)
    | ERestrictAssets o l b =>
        H_restrict_assets o l b (expr_ind o) (allows_ind l) (body_ind b)
    | EAs t e' => H_as t e' (expr_ind e')
    | EPrimWithSize p e' n => H_prim_with_size p e' n (expr_ind e')
    | EFromConsensusBuff t e' => H_from_consensus_buff t e' (expr_ind e')
    | EMap f e' => H_map f e' (expr_ind e')
    | EApp f args sp =>
        H_app f args sp (exprs_ind args)
          (match sp as sp' return Forall P (option_exprs sp') with
           | Some e' => Forall_cons e' (expr_ind e') (Forall_nil _)
           | None => Forall_nil _
           end)
    end.
End ExprInd.

Register Scheme expr_ind as ind_nodep for expr.

(** Two expressions of 2.5.3 and 3.3: [(match o ((some v) v) (none u0))]
    and [(as-max-len? s u4)]; and a call with a spread argument,
    [(f xs...)] (2.6.5). *)
Example expr_examples : list expr :=
  [EMatchOptional (EName "o") "v" (Body (EName "v") [])
     (Body (ELit (LUInt {| rval := 0%Z; rwf := eq_refl |})) []);
   EPrimWithSize AsMaxLen (EName "s")
     (SizeTermUInt {| rval := 4%Z; rwf := eq_refl |});
   EApp "f" [] (Some (EName "xs"))].
