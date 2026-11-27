(* Folding an operation mapping's structured body (R1-R3) at the boundaries
   of its integer types, and the spelling of the literals it folds to. *)

open Crane_plugin
open Base.Mapping_term
module It = Cpp_ir.Integer_type

let check name cond =
  if not cond then (
    Printf.eprintf "mapping_term: %s\n" name;
    exit 1 )

exception Failed

let fail _ = raise Failed
let z = Z.of_string
let two_63 = z "9223372036854775808"
let max_u64 = z "18446744073709551615"

let fold ?(arg_type = fun _ -> None) ?arg_literal e = fold ~fail ~arg_type ?arg_literal e
let fails e = match fold e with _ -> false | exception Failed -> true
let lit t v = Lit (t, z v)
let conv k t e = Convert (k, Int t, e)

let () =
  (* R1, Wrap: modulo two to the width, into the target's range. *)
  check "-1 wraps to uint8 255" (fold (conv Wrap U8 (lit I32 "-1")) = lit U8 "255");
  check "255 wraps to uint8 255" (fold (conv Wrap U8 (lit I32 "255")) = lit U8 "255");
  check "256 wraps to uint8 0" (fold (conv Wrap U8 (lit I32 "256")) = lit U8 "0");
  check "255 wraps to int8 -1" (fold (conv Wrap I8 (lit I32 "255")) = lit I8 "-1");
  check "-1 wraps to size_t 2^64-1" (fold (conv Wrap Size (lit I64 "-1")) = Lit (Size, max_u64));
  check "2^63 wraps to int64 min" (fold (conv Wrap I64 (Lit (U64, two_63))) = Lit (I64, Z.neg two_63));
  check "2^64-1 wraps to int64 -1" (fold (conv Wrap I64 (Lit (U64, max_u64))) = lit I64 "-1");
  check "char wrap is the platform's" (fold (conv Wrap Char (lit I32 "200")) = conv Wrap Char (lit I32 "200"));
  (* R1, Exact: the value, which must fit. *)
  check "2^64-1 is exactly a uint64" (fold (conv Exact U64 (Lit (U64, max_u64))) = Lit (U64, max_u64));
  check "2^63 is not an int64" (fails (conv Exact I64 (Lit (U64, two_63))));
  check "-1 is not a size_t" (fails (conv Exact Size (lit I32 "-1")));
  check "256 is not a uint8" (fails (conv Exact U8 (lit I32 "256")));
  check "255 is a uint8" (fold (conv Exact U8 (lit I32 "255")) = lit U8 "255");
  (* R1, Saturate: clamped. *)
  check "-1 saturates to uint8 0" (fold (conv Saturate U8 (lit I32 "-1")) = lit U8 "0");
  check "256 saturates to uint8 255" (fold (conv Saturate U8 (lit I32 "256")) = lit U8 "255");
  check "2^64-1 saturates to int64 max" (fold (conv Saturate I64 (Lit (U64, max_u64))) = Lit (I64, Z.pred two_63));
  (* R1 on an argument a use supplies as a literal. *)
  let u64 _ = Some It.U64 in
  check "a literal argument folds"
    (fold ~arg_type:u64 ~arg_literal:(fun _ -> Some (z "5")) (conv Exact Size (Arg 0)) = lit Size "5");
  check "a literal argument out of its type's range does not"
    (fold ~arg_type:(fun _ -> Some It.U8) ~arg_literal:(fun _ -> Some (z "256")) (conv Wrap Size (Arg 0))
     = conv Wrap Size (Arg 0));
  (* R2: a conversion to the operand's own type. *)
  check "uint64 to uint64 goes" (fold ~arg_type:u64 (conv Exact U64 (Arg 0)) = Arg 0);
  check "uint64 to size_t stays" (fold ~arg_type:u64 (conv Exact Size (Arg 0)) = conv Exact Size (Arg 0));
  check "an unknown type stays" (fold (conv Exact U64 (Arg 0)) = conv Exact U64 (Arg 0));
  check "uint8 + uint8 is an int"
    (let u8 _ = Some It.U8 in
     fold ~arg_type:u8 (conv Exact I32 (Binop (Add Unchecked, Arg 0, Arg 1))) = Binop (Add Unchecked, Arg 0, Arg 1));
  (* R3: an Exact conversion to a type holding the operand's values. *)
  let i32 _ = Some It.I32 in
  check "through a wider Exact"
    (fold ~arg_type:i32 (conv Wrap U8 (conv Exact I64 (Arg 0))) = conv Wrap U8 (Arg 0));
  check "size_t holds every uint64"
    (fold ~arg_type:u64 (conv Wrap U8 (conv Exact Size (Arg 0))) = conv Wrap U8 (Arg 0));
  check "never through Wrap"
    (fold ~arg_type:i32 (conv Wrap U8 (conv Wrap I64 (Arg 0))) = conv Wrap U8 (conv Wrap I64 (Arg 0)));
  check "not through a narrower Exact"
    (let i64 _ = Some It.I64 in
     fold ~arg_type:i64 (conv Wrap U8 (conv Exact I32 (Arg 0))) = conv Wrap U8 (conv Exact I32 (Arg 0)));
  (* Literals, as C++ spells them. *)
  check "size_t literal" (It.spell_literal Size (z "5") = "5uz");
  check "uint64 max" (It.spell_literal U64 max_u64 = "UINT64_C(18446744073709551615)");
  check "int64 min" (It.spell_literal I64 (Z.neg two_63) = "INT64_MIN");
  check "int64 -1" (It.spell_literal I64 (z "-1") = "INT64_C(-1)");
  check "int -1" (It.spell_literal I32 (z "-1") = "-1");
  check "uint8 255" (It.spell_literal U8 (z "255") = "uint8_t{255}");
  check "uint32" (It.spell_literal U32 (z "1") = "1u");
  (* The text the legacy readers see. *)
  check "text"
    (text (Cond (Binop (Less, Arg 0, Arg 1), Convert (Exact, Int Size, Arg 0), lit I32 "0"))
     = "((%a0 < %a1) ? static_cast<std::size_t>(%a0) : 0)");
  check "a member of an argument" (text (Member (Arg 0, "first")) = "%a0.first")
