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
