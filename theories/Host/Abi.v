(** * Value interpretation layer

    The value layer of the chain ABI the language spec relies on
    ([clarity-vision/08-value-interpretation.md]): canonical encoding
    (section 3), [serialized-size] (4.1), the [abi.types] section (5),
    trait conformance (5.2), argument and result encoding (6), event data
    (7.1), and the storage layout (7.2). Kept abstract while the document is a
    proposal. *)

From ClarityCert Require Import
  Common.Base
  Syntax.Types
  Syntax.Values.
