(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Names
open Miniml
open Ml_type_util

let rec strip_magic = function MLmagic (_, e) -> strip_magic e | e -> e

let registered_constructor name = function
  | GlobRef.ConstructRef (ind, idx) when Rocqlib.has_ref name && Rocqlib.check_ref name (GlobRef.IndRef ind) ->
    Some idx
  | _ -> None

(* A [Decimal.uint] digit chain, most significant digit outermost, onto
   [acc]. *)
let rec decimal_uint expr acc =
  match strip_magic expr with
  | MLcons (_, r, args) -> (
    match (registered_constructor "num.uint.type" r, args) with
    | Some idx, [] when idx = uint_nil_idx -> Some acc
    | Some cidx, [inner] when cidx >= decimal_d0_idx && cidx <= decimal_d9_idx ->
      let digit = Z.of_int (cidx - decimal_d0_idx) in
      decimal_uint inner Z.((acc * of_int 10) + digit)
    | _ -> None )
  | _ -> None

(* A [Decimal.signed_int]: [Pos] or [Neg] of a [Decimal.uint] chain. *)
let signed_decimal_int expr =
  match strip_magic expr with
  | MLcons (_, r, [inner]) -> (
    match registered_constructor "num.int.type" r with
    | Some idx when idx = signed_pos_idx -> decimal_uint inner Z.zero
    | Some idx when idx = signed_neg_idx -> Option.map Z.neg (decimal_uint inner Z.zero)
    | _ -> None )
  | _ -> None

(* A [Hexadecimal.uint] digit chain onto [acc]. *)
let rec hex_uint expr acc =
  match strip_magic expr with
  | MLcons (_, r, args) -> (
    match (registered_constructor "num.hexadecimal_uint.type" r, args) with
    | Some idx, [] when idx = uint_nil_idx -> Some acc
    | Some cidx, [inner] when cidx >= hex_d0_idx && cidx <= hex_df_idx ->
      let digit = Z.of_int (cidx - hex_d0_idx) in
      hex_uint inner Z.((acc * of_int 16) + digit)
    | _ -> None )
  | _ -> None

(* A [Hexadecimal.signed_int]: [Pos] or [Neg] of a [Hexadecimal.uint]
   chain. *)
let signed_hex_int expr =
  match strip_magic expr with
  | MLcons (_, r, [inner]) -> (
    match registered_constructor "num.hexadecimal_int.type" r with
    | Some idx when idx = signed_pos_idx -> hex_uint inner Z.zero
    | Some idx when idx = signed_neg_idx -> Option.map Z.neg (hex_uint inner Z.zero)
    | _ -> None )
  | _ -> None

(* A [Number.int]: [IntDecimal] or [IntHexadecimal]. *)
let num_int expr =
  match strip_magic expr with
  | MLcons (_, r, [inner]) -> (
    match registered_constructor "num.num_int.type" r with
    | Some 1 -> signed_decimal_int inner
    | Some 2 -> signed_hex_int inner
    | _ -> None )
  | _ -> None

(* A [Number.uint]: [UIntDecimal] or [UIntHexadecimal]. *)
let num_uint expr =
  match strip_magic expr with
  | MLcons (_, r, [inner]) -> (
    match registered_constructor "num.num_uint.type" r with
    | Some idx when idx = num_uint_decimal_idx -> decimal_uint inner Z.zero
    | Some idx when idx = num_uint_hex_idx -> hex_uint inner Z.zero
    | _ -> None )
  | _ -> None

let converter_literal r arg =
  match Option.bind (Table.numeral_ind_of_converter r) Table.get_numeral_info with
  | None -> None
  | Some info -> (
    match num_uint arg with
    | Some n -> Some (info, n)
    | None -> Option.map (fun n -> (info, n)) (num_int arg) )

let fold = function
  | MLapp (MLglob {callee = r; _}, [arg]) as e -> (
    match converter_literal r arg with
    | Some (info, n) -> MLnumeral (info.Table.num_ind, n)
    | None -> e )
  | e -> e

let folds = function
  | MLapp (MLglob {callee = r; _}, [arg]) -> Option.has_some (converter_literal r arg)
  | _ -> false
