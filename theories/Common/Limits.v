(** * Language limits

    Language-level limits (spec 2.8): value and intermediate size limits,
    fixpoint step limit, type depth, identifier length, function call
    depth within a contract, allowances per frame, storage key size. The
    contract-call depth limit and the transaction's event bytes belong to
    the chain ABI. *)

From ClarityCert Require Import
  Common.Base.

(** Limits are binary naturals: byte counts reach 2^23, too large for a
    unary [nat]. Proofs should rely on the lemmas below rather than on
    the values, two of which the spec marks as provisional. *)

Local Open Scope N_scope.

(** Maximum [serialized-size] of the type of a name, a function result, a
    type written in source, or a stored, emitted or passed value
    (2.3.1). It is also the chain ABI's event data limit, so it bounds
    the declared type of every event (2.4.1, 3.10). *)
Definition max_value_size : N := 1048576.

(** Maximum [serialized-size] of the type of any other expression
    (2.3.1). Provisional. *)
Definition max_intermediate_size : N := 8388608.

(** Steps allowed for a fold accumulator's type to reach its fixpoint
    (2.6.2). Provisional. *)
Definition fixpoint_step_limit : N := 8.

(** Maximum type nesting depth. *)
Definition max_type_depth : N := 32.

(** Maximum identifier length, in bytes (2.2). *)
Definition max_identifier_length : N := 128.

(** Maximum function call depth within a contract, enforced statically
    (2.7.5). *)
Definition max_call_depth : N := 128.

(** Maximum allowances per [as-contract?] or [restrict-assets?]
    (2.5.9). *)
Definition max_allowances : N := 128.

(** Maximum storage key: a map's key prefix plus the [serialized-size] of
    its key type, in bytes (3.7). *)
Definition max_storage_key_size : N := 1024.

(** A value that fits the value size limit also fits the intermediate one,
    so a bound or stored value can always appear as an intermediate
    expression (2.3.1). *)
Lemma max_value_size_le_intermediate :
  max_value_size <= max_intermediate_size.
Proof. apply N.leb_le. reflexivity. Qed.
