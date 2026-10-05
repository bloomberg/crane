(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Names

type width = W8 | W16 | W32 | W64

type unsigned_op = Add | Mul | Sub_truncated | Div | Mod | Eqb | Ltb | Leb | Max | Min

type t =
  | Unsigned_nat of width
  | Unsigned of unsigned_op * width
  | Ref_new of int
  | Ref_read of int
  | Ref_write of int * int

let bits = function W8 -> 8 | W16 -> 16 | W32 -> 32 | W64 -> 64

let max_value w = Z.pred (Z.shift_left Z.one (bits w))

let table : t GlobRef.Map.t ref =
  Summary.ref GlobRef.Map.empty ~name:"CraneExtrSemantics"

let find r = GlobRef.Map.find_opt r !table

let semantics_object : GlobRef.t * t -> Libobject.obj =
  let open Libobject in
  declare_object
  @@ superglobal_object "Crane Semantics"
       ~cache:(fun (r, s) -> table := GlobRef.Map.add r s !table)
       ~subst:(Some (fun (sub, (r, s)) -> (fst (Globnames.subst_global sub r), s)))
       ~discharge:(fun x -> Some x)

let error msg = CErrors.user_err Pp.(str "Crane Semantics: " ++ str msg)

let parse_width = function
  | "8" -> W8 | "16" -> W16 | "32" -> W32 | "64" -> W64
  | w -> error ("unsupported width " ^ w ^ "; expected 8, 16, 32 or 64")

let parse_op = function
  | "add" -> Add | "mul" -> Mul | "sub_truncated" -> Sub_truncated
  | "div" -> Div | "mod" -> Mod | "eqb" -> Eqb | "ltb" -> Ltb | "leb" -> Leb
  | "max" -> Max | "min" -> Min
  | op -> error ("unknown unsigned operation " ^ op)

let position s =
  match int_of_string_opt s with
  | Some n when n >= 0 -> n
  | _ -> error ("expected an argument position, not " ^ s)

let parse words =
  match List.filter (( <> ) "") (String.split_on_char ' ' words) with
  | ["unsigned_nat"; w] -> Unsigned_nat (parse_width w)
  | ["unsigned"; op; w] -> Unsigned (parse_op op, parse_width w)
  | ["ref"; "new"; v] -> Ref_new (position v)
  | ["ref"; "read"; c] -> Ref_read (position c)
  | ["ref"; "write"; c; v] -> Ref_write (position c, position v)
  | _ ->
    error
      ("cannot read \"" ^ words
     ^ "\"; expected \"unsigned_nat W\", \"unsigned OP W\", \"ref new V\", \
        \"ref read C\" or \"ref write C V\"")

(* An [Unsigned_nat] type is [O | S n]: two constructors, the first constant
   and the second taking one argument -- the order the passes that read the
   declaration rely on. *)
let check_nat_shape r =
  match r with
  | GlobRef.IndRef ind ->
    let _, oib = Inductive.lookup_mind_specif (Global.env ()) ind in
    if oib.Declarations.mind_consnrealargs <> [| 0; 1 |] then
      error "an unsigned_nat type has two constructors, O and then S n"
  | _ -> error "unsigned_nat names an inductive type"

let declare q words =
  let r = Smartlocate.global_with_alias q in
  let s = parse words in
  ( match s with
  | Unsigned_nat _ -> check_nat_shape r
  | Unsigned _ | Ref_new _ | Ref_read _ | Ref_write _ -> (
    match r with
    | GlobRef.ConstRef _ -> ()
    | _ -> error "an operation names a constant" ) );
  Lib.add_leaf (semantics_object (r, s))

let nat_width ind =
  match find (GlobRef.IndRef ind) with Some (Unsigned_nat w) -> Some w | _ -> None
