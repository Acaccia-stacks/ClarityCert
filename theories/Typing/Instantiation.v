(** * Instantiation and overload resolution

    Instantiations as substitutions over type, size and reference
    variables; reference arguments matched by kind, with identical types
    except for [(event T)], whose declared type may be a supertype
    (2.3.7); least instantiation, read through the join; the capped
    fold-accumulator fixpoint, with the referenced definition fixed for
    the whole fixpoint; and overload resolution for calls and for
    function references (spec 2.6.2). Instances are what typing and
    compilation operate on; the definition graph is over names and is
    checked before any instance exists (2.4.3). *)

From ClarityCert Require Import
  Common.Base
  Common.Limits
  Syntax.Types
  Syntax.Ast
  Typing.Subtyping
  Primitives.Signatures.
