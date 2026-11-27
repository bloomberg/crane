(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The integer types of an operation mapping's structured body
    ({!Grammar.Integer_type}): their spelling, range, and literals. *)

include Grammar.Integer_type

(** The C++ spelling, as the typed mappings of [nat], [N], [Z] and the
    primitive integers spell their canonical types. *)
let spelling = function
  | I8 -> "int8_t"
  | I16 -> "int16_t"
  | I32 -> "int32_t"
  | I64 -> "int64_t"
  | U8 -> "uint8_t"
  | U16 -> "uint16_t"
  | U32 -> "uint32_t"
  | U64 -> "uint64_t"
  | Size -> "std::size_t"
  | Char -> "char"
  | Uchar -> "unsigned char"

let all = [I8; I16; I32; I64; U8; U16; U32; U64; Size; Char; Uchar]

let width = function
  | I8 | U8 | Char | Uchar -> 8
  | I16 | U16 -> 16
  | I32 | U32 -> 32
  | I64 | U64 | Size -> 64

(** Whether the type is signed; [char]'s signedness is the platform's, so it
    is neither. *)
let signed = function I8 | I16 | I32 | I64 -> Some true | U8 | U16 | U32 | U64 | Size | Uchar -> Some false | Char -> None

(** The values every platform's type holds: [char] holds [0..127] on every
    platform; [std::size_t] is taken as 64 bits wide. *)
let range t =
  let p k = Z.shift_left Z.one k in
  match t with
  | Char -> (Z.zero, Z.of_int 127)
  | _ -> (
    let w = width t in
    match signed t with
    | Some true -> (Z.neg (p (w - 1)), Z.pred (p (w - 1)))
    | _ -> (Z.zero, Z.pred (p w)) )

let fits t v =
  let lo, hi = range t in
  Z.leq lo v && Z.leq v hi

(** Whether every value of [a] is a value of [b]. *)
let includes b a =
  let lo_a, hi_a = range a and lo_b, hi_b = range b in
  Z.leq lo_b lo_a && Z.leq hi_a hi_b

(** [v] reduced modulo two to the width of [t] into its range, as C++
    converts an integer to [t]; [None] for [char], whose result is the
    platform's. *)
let wrap t v =
  match signed t with
  | None -> None
  | Some s ->
    let w = width t in
    let m = Z.extract v 0 w in
    if s && Z.testbit m (w - 1) then Some (Z.sub m (Z.shift_left Z.one w)) else Some m

(** [v] clamped to the range of [t]. *)
let saturate t v =
  let lo, hi = range t in
  if Z.lt v lo then lo else if Z.gt v hi then hi else v

(** Whether the literal [v] of type [t] prints as a prefix [-]. *)
let literal_is_negative v = Z.sign v < 0

(** The C++ spelling of the literal [v] of type [t], [v] in its range: a
    [std::size_t] is [Nuz]; [int64_t] and [uint64_t] are the [<cstdint>]
    macros [nat] and [int] numerals use; [int32_t] is a plain literal,
    [uint32_t] one with [u]; the narrow types are braced. *)
let spell_literal t v =
  let s = Z.to_string v in
  match t with
  | Size -> s ^ "uz"
  | I64 when Z.equal v (fst (range I64)) -> "INT64_MIN"
  | I64 -> "INT64_C(" ^ s ^ ")"
  | U64 -> "UINT64_C(" ^ s ^ ")"
  | I32 when Z.equal v (fst (range I32)) -> "INT32_MIN"
  | I32 -> s
  | U32 -> s ^ "u"
  | I8 | I16 | U8 | U16 | Char | Uchar -> spelling t ^ "{" ^ s ^ "}"
