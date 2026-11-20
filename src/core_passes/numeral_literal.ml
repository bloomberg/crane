(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Names
open Base.Type_util

let strip_magic = Core.Expr.strip_crossings

let registered_constructor name = function
  | GlobRef.ConstructRef (ind, idx) when Rocqlib.has_ref name && Rocqlib.check_ref name (GlobRef.IndRef ind) ->
    Some idx
  | _ -> None

(* A [Decimal.uint] digit chain, most significant digit outermost, onto
   [acc]. *)
let rec decimal_uint expr acc =
  match strip_magic expr with
  | Core.Expr.Construct {constructor = r; arguments = args; _} -> (
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
  | Core.Expr.Construct {constructor = r; arguments = [inner]; _} -> (
    match registered_constructor "num.int.type" r with
    | Some idx when idx = signed_pos_idx -> decimal_uint inner Z.zero
    | Some idx when idx = signed_neg_idx -> Option.map Z.neg (decimal_uint inner Z.zero)
    | _ -> None )
  | _ -> None

(* A [Hexadecimal.uint] digit chain onto [acc]. *)
let rec hex_uint expr acc =
  match strip_magic expr with
  | Core.Expr.Construct {constructor = r; arguments = args; _} -> (
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
  | Core.Expr.Construct {constructor = r; arguments = [inner]; _} -> (
    match registered_constructor "num.hexadecimal_int.type" r with
    | Some idx when idx = signed_pos_idx -> hex_uint inner Z.zero
    | Some idx when idx = signed_neg_idx -> Option.map Z.neg (hex_uint inner Z.zero)
    | _ -> None )
  | _ -> None

(* A [Number.int]: [IntDecimal] or [IntHexadecimal]. *)
let num_int expr =
  match strip_magic expr with
  | Core.Expr.Construct {constructor = r; arguments = [inner]; _} -> (
    match registered_constructor "num.num_int.type" r with
    | Some 1 -> signed_decimal_int inner
    | Some 2 -> signed_hex_int inner
    | _ -> None )
  | _ -> None

(* A [Number.uint]: [UIntDecimal] or [UIntHexadecimal]. *)
let num_uint expr =
  match strip_magic expr with
  | Core.Expr.Construct {constructor = r; arguments = [inner]; _} -> (
    match registered_constructor "num.num_uint.type" r with
    | Some idx when idx = num_uint_decimal_idx -> decimal_uint inner Z.zero
    | Some idx when idx = num_uint_hex_idx -> hex_uint inner Z.zero
    | _ -> None )
  | _ -> None

let converter_literal r arg =
  match Option.bind (Base.Table.numeral_ind_of_converter r) Base.Table.get_numeral_info with
  | None -> None
  | Some info -> (
    match num_uint arg with
    | Some n -> Some (info, n)
    | None -> Option.map (fun n -> (info, n)) (num_int arg) )

(* A binary [positive] chain [xI (xO (... xH))]. *)
let rec positive expr =
  match strip_magic expr with
  | Core.Expr.Construct {constructor = r; arguments = args; _} -> (
    match (registered_constructor "num.pos.type" r, args) with
    | Some idx, [] when idx = positive_xH_idx -> Some Z.one
    | Some idx, [inner] when idx = positive_xI_idx -> Option.map (fun n -> Z.succ (Z.shift_left n 1)) (positive inner)
    | Some idx, [inner] when idx = positive_xO_idx -> Option.map (fun n -> Z.shift_left n 1) (positive inner)
    | _ -> None )
  | _ -> None

(* A Peano chain of [info]'s inductive: its successor constructor down to
   its zero constructor. *)
let rec peano info expr =
  let index = function
    | GlobRef.ConstructRef (ind, cidx) when GlobRef.CanOrd.equal (GlobRef.IndRef ind) info.Base.Table.ind ->
      Some cidx
    | _ -> None
  in
  match strip_magic expr with
  | Core.Expr.Construct {constructor = cr; arguments = []; _} when index cr = Some info.Base.Table.zero_ctor ->
    Some Z.zero
  | Core.Expr.Construct {constructor = cr; arguments = [inner]; _} when index cr = Some info.Base.Table.succ_ctor ->
    Option.map Z.succ (peano info inner)
  | _ -> None

(* Whether [r] is the global Rocq registers as [name]. *)
let registered name r = Rocqlib.has_ref name && Rocqlib.check_ref name r

(* The value of a constructor term of a typed numeral descriptor's type,
   by its constructors' actions (design 17): a field another numeral type
   (an [Identity] or a [Negate]) is read by that type's own descriptor, or
   as a binary [positive] where its type has none. *)
let rec typed_value expr =
  match strip_magic expr with
  | Core.Expr.Construct {constructor = GlobRef.ConstructRef ((kn, i), j); arguments = args; _} as e -> (
    match Base.Table.get_numeral_info (GlobRef.IndRef (kn, i)) with
    | Some {typed = Some cases; _} -> (
      let field f = Option.bind (List.nth_opt args f) typed_value in
      match List.assoc_opt j cases with
      | Some Base.Mapping_descriptor.Numeral_zero -> Some Z.zero
      | Some Numeral_one -> Some Z.one
      | Some (Numeral_successor f) -> Option.map Z.succ (field f)
      | Some (Numeral_double f) -> Option.map (fun n -> Z.shift_left n 1) (field f)
      | Some (Numeral_double_plus_one f) -> Option.map (fun n -> Z.succ (Z.shift_left n 1)) (field f)
      | Some (Numeral_identity f) -> field f
      | Some (Numeral_negate f) -> Option.map Z.neg (field f)
      | None -> None )
    | _ -> positive e )
  | _ -> None

let constructor_literal = function
  | Core.Expr.Construct {constructor = (GlobRef.ConstructRef ((kn, i), _) as r); arguments = args; _} as e -> (
    let ind = GlobRef.IndRef (kn, i) in
    match Base.Table.get_numeral_info ind with
    | None -> None
    | Some ({typed = Some _; _} as info) -> Option.map (fun n -> (info, n)) (typed_value e)
    | Some info when registered "num.pos.type" ind -> Option.map (fun n -> (info, n)) (positive e)
    | Some info -> (
      match (peano info e, args) with
      | Some n, _ -> Some (info, n)
      | None, [inner] when registered "num.Z.Zpos" r || registered "num.N.Npos" r ->
        Option.map (fun p -> (info, p)) (positive inner)
      | None, [inner] when registered "num.Z.Zneg" r -> Option.map (fun p -> (info, Z.neg p)) (positive inner)
      | None, _ -> None ) )
  | _ -> None

(* The numeral mapping and value of [e], where {!fold} writes it as a
   literal: a converter applied to one digit chain, or a constructor term. *)
let literal = function
  | Core.Expr.Apply {callee = Core.Expr.Global {callee = r; _}; arguments = [arg]} -> converter_literal r arg
  | Core.Expr.Construct _ as e -> constructor_literal e
  | _ -> None

(* Rocq's Euclidean quotient and remainder of [nat], [N] and [Z], keyed on
   canonical names, so a use through a module that [Include]s the defining
   one ([PeanoNat.Nat.div]) is found. *)
type division = Quotient | Remainder

let divisions =
  let nat = Base.Core_util.con_in_file "Corelib.Init.Nat" in
  let n = Base.Core_util.con_in_module "Stdlib.NArith.BinNatDef" "N" in
  let z = Base.Core_util.con_in_module "Corelib.BinNums.IntDef" "Z" in
  List.fold_left
    (fun m (c, d) -> Cmap.add c d m)
    Cmap.empty
    [ (nat "div", Quotient); (nat "modulo", Remainder);
      (n "div", Quotient); (n "modulo", Remainder);
      (z "div", Quotient); (z "modulo", Remainder) ]

(* A division by a literal, as the value it computes: dividing by zero
   gives a quotient of zero and leaves the dividend as the remainder, and a
   literal divided by another is the literal of its floored quotient or
   remainder.  The dividend is pure and total, so leaving it out loses
   nothing. *)
let division = function
  | Core.Expr.Apply {callee = Core.Expr.Global {callee = GlobRef.ConstRef c; _}; arguments = [a; b]} as e -> (
    match (Cmap.find_opt c divisions, strip_magic b) with
    | Some d, Core.Expr.Numeral {inductive; value = divisor} -> (
      let literal value = Core.Expr.Numeral {inductive; value} in
      match (d, strip_magic a) with
      | Quotient, _ when Z.equal divisor Z.zero -> literal Z.zero
      | Remainder, _ when Z.equal divisor Z.zero -> a
      | Quotient, Core.Expr.Numeral {value = n; _} -> literal (Z.fdiv n divisor)
      | Remainder, Core.Expr.Numeral {value = n; _} -> literal Z.(n - (divisor * fdiv n divisor))
      | _ -> e )
    | _ -> e )
  | e -> e

(* The value Rocq gives the subtraction of [nat], [N], [positive] and [Z]
   of one number from itself, as the constant constructor that spells it,
   with its inductive: zero, but one for [positive], whose subtraction stops
   at one. *)
let self_subtractions =
  let nat = Base.Core_util.con_in_file "Corelib.Init.Nat" in
  let n = Base.Core_util.con_in_module "Corelib.BinNums.NatDef" "N" in
  let pos = Base.Core_util.con_in_module "Corelib.BinNums.PosDef" "Pos" in
  let z = Base.Core_util.con_in_module "Corelib.BinNums.IntDef" "Z" in
  List.fold_left
    (fun m (c, v) -> Cmap.add c v m)
    Cmap.empty
    [ (nat "sub", ("num.nat.type", "num.nat.O")); (n "sub", ("num.N.type", "num.N.N0"));
      (pos "sub", ("num.pos.type", "num.pos.xH")); (z "sub", ("num.Z.type", "num.Z.Z0")) ]

(* A subtraction of one read of storage from itself
   ({!Base.Core_util.same_storage}), as the value it computes, a literal
   where its number type is a numeral mapping's: a mapping's guard would
   compare the read with itself. *)
let self_subtraction = function
  | Core.Expr.Apply {callee = Core.Expr.Global {callee = GlobRef.ConstRef c; _}; arguments = [a; b]} as e
    when Base.Core_util.same_storage a b -> (
    match Cmap.find_opt c self_subtractions with
    | Some (ind, ctor) when Rocqlib.has_ref ind && Rocqlib.has_ref ctor ->
      let value =
        Core.Expr.Construct
          { result_type =
              Core.Type.Global_app {head = Rocqlib.lib_ref ind; type_arguments = []; index_arguments = []};
            constructor = Rocqlib.lib_ref ctor;
            arguments = [];
            occurrence = Core.Occurrence.fresh () }
      in
      ( match constructor_literal value with
      | Some (info, n) -> Core.Expr.Numeral {inductive = info.Base.Table.ind; value = n}
      | None -> value )
    | _ -> e )
  | e -> e

let fold e =
  match literal e with
  | Some (info, n) -> Core.Expr.Numeral {inductive = info.Base.Table.ind; value = n}
  | None -> self_subtraction (division e)

let folds e = Option.has_some (literal e)

let converter_folds = function
  | Core.Expr.Apply {callee = Core.Expr.Global {callee = r; _}; arguments = [arg]} ->
    Option.has_some (converter_literal r arg)
  | _ -> false
