(** * Types

    The type grammar, including [never] (spec 2.3.3) and the internal
    contract-literal type, sequence types and element types (2.3.1), the
    storable / interface type predicates (2.3.4), type and size variables
    and static constants as sizes (2.3.5), aliases (2.3.6), and static
    reference kinds, including [(event T)] (2.3.7). *)

From ClarityVerif Require Import
  Common.Base
  Common.Limits.
