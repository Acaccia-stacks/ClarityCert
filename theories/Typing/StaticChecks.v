(** * Static checks

    Contract-level static rules: a declared version the checker
    implements (spec 2.4.0); one namespace for top-level names, shared
    only by overloads (2.4); acyclic definition graph over names, checked
    before instantiation (2.4.3); definitions used at deploy come first
    and no [return] at top level (2.4.2); reserved names and prelude
    names never redefined, no shadowing (2.2, 2.4.5, 2.5.2); intermediate
    responses handled and [impl-trait] conformance against declared
    signatures (2.4.1, 2.5.8); overloads that do not overlap (2.6.2); the
    function call depth limit, enforced statically (2.7.5, 2.8);
    read-only enforcement (2.7.4). A missing version declaration and a
    bound keyword are parse errors, not checked here (chapter 5); the
    static errors chapter 5.4 lists (C1-C15) are checked here or in
    [Typing.Typing]. *)

From ClarityVerif Require Import
  Common.Base
  Syntax.Ast
  Typing.Typing.
