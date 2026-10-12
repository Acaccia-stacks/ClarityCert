(** * Typing judgments

    Typing of expressions and definitions on instances (spec 2.5, 2.6.4):
    [let], [match], [and]/[or], [return], constructors, tuple access,
    [contract-call?], [as-contract?]/[restrict-assets?], [as]; result type
    inference; value and intermediate size limits. *)

From ClarityVerif Require Import
  Common.Base
  Common.Limits
  Syntax.Types
  Syntax.Ast
  Host.Abi
  Typing.Subtyping
  Typing.Instantiation
  Typing.Inline
  Primitives.Signatures.
