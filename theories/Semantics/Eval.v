(** * Dynamic semantics

    Evaluation of instances (spec 2.7): strict left-to-right evaluation,
    outcomes (value, early [return], abort), rollback of every public
    function invocation, internal calls included (2.6.1, 2.7.3), context
    frames, depth and reentrancy, deploy-time code in source order
    (2.4.2). *)

From ClarityVerif Require Import
  Common.Base
  Common.Limits
  Syntax.Values
  Syntax.Ast
  Host.Interface
  Semantics.State
  Semantics.Allowances
  Primitives.Arith
  Primitives.Sequences
  Primitives.Conversions
  Primitives.Principals
  Primitives.Crypto
  Primitives.Storage
  Primitives.Assets
  Primitives.Context
  Primitives.Control.
