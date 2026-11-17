(** * Typing judgments

    Typing of expressions and definitions on instances (spec 2.5, 2.6.4):
    [let], [match], [and]/[or], [return], constructors, tuple access,
    [contract-call?] and [contract-call-raw?],
    [as-contract?]/[restrict-assets?], [as]; how [never] operands are
    typed (2.3.3); result type inference; value and intermediate size
    limits. *)

From ClarityCert Require Import
  Common.Base
  Common.Limits
  Syntax.Types
  Syntax.Ast
  Host.Abi
  Typing.Subtyping
  Typing.Instantiation
  Typing.Macros
  Primitives.Signatures.
