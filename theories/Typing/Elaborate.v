(** * Elaboration

    Elaboration turns the source syntax ([Syntax.Ast]) into the form the
    type checker and the semantics work on: names in types, sizes,
    contracts and traits are resolved against the contract being
    deployed. Its context is the deployer, the aliases (2.3.6), the
    static constants (2.4.1), the type and size variables in scope
    (2.3.5) and the traits the contract defines. It runs after the
    name-level static checks, which make the names it resolves unique
    (2.4). *)

From ClarityCert Require Import
  Common.Base
  Syntax.Principals
  Syntax.Values
  Syntax.Ast.

(** ** Contracts and literals

    A contract named relative to the deployer, [.c], is the contract [c]
    of the deployer (spec 2.2). The validity of [c] is carried over from
    the source name, so resolution needs no new proof. Every other
    literal denotes its value as is: the lexer has already checked its
    range ([Syntax.Ast]). *)

Definition resolve_contract (deployer : standard_principal)
    (c : src_contract) : contract_id :=
  match c with
  | ContractAbs c => c
  | ContractRel n => {| ci_issuer := deployer; ci_name := rval n; ci_wf := rwf n |}
  end.

(** The value a literal denotes in a contract deployed by [deployer]. *)
Definition literal_value (deployer : standard_principal) (l : literal) : value :=
  match l with
  | LInt i => VInt i
  | LUInt u => VUInt u
  | LBool b => VBool b
  | LBuff bs => VBuff bs
  | LAscii s => VAscii s
  | LUtf8 s => VUtf8 s
  | LPrincipal p => VPrincipal (PStandard p)
  | LContract c => VPrincipal (PContract (resolve_contract deployer c))
  | LNone => VNone
  end.

(** [.counter], deployed by [example_principal], is [example_contract].
    The same contract written in full is the same value. *)
Example literal_examples :
  literal_value example_principal example_contract_literal
  = VPrincipal (PContract example_contract)
  /\ literal_value example_principal (LContract (ContractAbs example_contract))
     = VPrincipal (PContract example_contract).
Proof. split; reflexivity. Qed.
