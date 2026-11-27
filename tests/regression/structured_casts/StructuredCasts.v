From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Crane Require Import Mapping.Descriptor Mapping.Cpp.
From Crane Require Extraction.
From Corelib Require Import PrimString.
From Stdlib Require Import List ZArith.
Import ListNotations Crane.Cpp.
Open Scope Z_scope.
Local Open Scope pstring_scope.

(** Operation mappings with structured bodies converting at the boundaries
    of their integer types.  Crane folds a conversion of a literal into a
    literal of the target type (here at every call with a literal
    argument), drops a conversion to the type its operand has, and drops
    an [Exact] conversion to a type wide enough under another conversion;
    the C++ test checks the folded constants against the same operations
    applied at run time. *)
Axiom wrap_u8 : Z -> Z.
Axiom wrap_i8 : Z -> Z.
Axiom sat_u8 : Z -> Z.
Axiom sat_i8 : Z -> Z.
Axiom is_size_max : Z -> bool.
Axiom is_u64_max : nat -> bool.
Axiom low_byte : nat -> Z.
Axiom same : Z -> Z.
Axiom min_from_wrap : bool.

#[export] Instance wrap_u8_mapping : OperationMapping (Ref wrap_u8) :=
  pure [] ["z"] (Convert Exact ResultType (wrap U8 (Arg "z"))).
#[export] Instance wrap_i8_mapping : OperationMapping (Ref wrap_i8) :=
  pure [] ["z"] (Convert Exact ResultType (wrap I8 (Arg "z"))).
#[export] Instance sat_u8_mapping : OperationMapping (Ref sat_u8) :=
  pure ["numeric"] ["z"] (Convert Exact ResultType (Convert Saturate (Int U8) (Arg "z"))).
#[export] Instance sat_i8_mapping : OperationMapping (Ref sat_i8) :=
  pure ["numeric"] ["z"] (Convert Exact ResultType (Convert Saturate (Int I8) (Arg "z"))).
(** -1 wrapped to [std::size_t] is its largest value. *)
#[export] Instance is_size_max_mapping : OperationMapping (Ref is_size_max) :=
  pure ["cstddef"] ["z"] (Binop Equal (wrap Size (Arg "z")) (IntLit Size 18446744073709551615)).
#[export] Instance is_u64_max_mapping : OperationMapping (Ref is_u64_max) :=
  pure [] ["n"] (Binop Equal (Arg "n") (IntLit U64 18446744073709551615)).
(** R3: [std::size_t] holds every [uint64_t], so the inner conversion goes. *)
#[export] Instance low_byte_mapping : OperationMapping (Ref low_byte) :=
  pure ["cstddef"] ["n"] (Convert Exact ResultType (wrap U8 (exact Size (Arg "n")))).
(** R2: the argument is an [int64_t] already. *)
#[export] Instance same_mapping : OperationMapping (Ref same) :=
  pure [] ["z"] (exact I64 (Arg "z")).
(** 2^63 wrapped to [int64_t] is its least value. *)
#[export] Instance min_from_wrap_mapping : OperationMapping (Ref min_from_wrap) :=
  pure [] []
    (Binop Equal (wrap I64 (IntLit U64 9223372036854775808)) (IntLit I64 (-9223372036854775808))).

Module StructuredCasts.

Definition f_wrap_u8 (z : Z) : Z := wrap_u8 z.
Definition f_wrap_i8 (z : Z) : Z := wrap_i8 z.
Definition f_sat_u8 (z : Z) : Z := sat_u8 z.
Definition f_sat_i8 (z : Z) : Z := sat_i8 z.
Definition f_is_size_max (z : Z) : bool := is_size_max z.
Definition f_is_u64_max (n : nat) : bool := is_u64_max n.
Definition f_low_byte (n : nat) : Z := low_byte n.
Definition f_same (z : Z) : Z := same z.

Definition wrap_u8_m1 : Z := wrap_u8 (-1).
Definition wrap_u8_255 : Z := wrap_u8 255.
Definition wrap_u8_256 : Z := wrap_u8 256.
Definition wrap_i8_m1 : Z := wrap_i8 (-1).
Definition wrap_i8_128 : Z := wrap_i8 128.
Definition wrap_i8_255 : Z := wrap_i8 255.
Definition sat_u8_m1 : Z := sat_u8 (-1).
Definition sat_u8_256 : Z := sat_u8 256.
Definition sat_i8_m129 : Z := sat_i8 (-129).
Definition sat_i8_128 : Z := sat_i8 128.
Definition size_max_constant : bool := is_size_max (-1).
Definition low_byte_constant : Z := low_byte 257.
Definition min_constant : bool := min_from_wrap.

End StructuredCasts.

Crane Extraction "structured_casts" StructuredCasts.
