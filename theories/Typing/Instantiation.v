(** * Instantiation and overload resolution

    Instantiations as substitutions over type, size and reference
    variables; least instantiation, the capped fold-accumulator fixpoint,
    and overload resolution (spec 2.6.2). Instances are what typing,
    compilation and the definition graph operate on. *)

From ClarityVerif Require Import
  Common.Base
  Common.Limits
  Syntax.Types
  Syntax.Ast
  Typing.Subtyping
  Primitives.Signatures.
