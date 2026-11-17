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
  Syntax.Types
  Syntax.Values.
