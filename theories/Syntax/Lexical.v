(** * Lexical structure

    Well-formedness of identifiers, literals (including the [string-ascii]
    character set and the one spelling of each [\u{H}] escape), principal
    literals and contract names; keywords and reserved names (spec 2.2).
    These are the token rules of the grammar's Part L, the character set
    (T3) and the lexical checks LX1-LX7 (chapter 5), stated as predicates
    for the lexer to be proved against. *)

From ClarityVerif Require Import
  Common.Base
  Common.Limits.
