(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** An operation mapping's structured body ({!Base.Mapping_term}) lowered at
    one use.  See [structured_operation.mli]. *)

open Names
module T = Base.Mapping_term

type ty = Cpp_ir.Lowered.Type.t
type expr = Cpp_ir.Lowered.Expr.t

(* The value of an integer literal a use supplies as an argument. *)
let literal_value (e : expr) : Z.t option =
  match e with
  | Numeral (_, n) -> Some n.value
  | Literal (Integer (_, v)) -> Some v
  | Literal (Int n) -> Some (Z.of_int n)
  | Literal (Uint63 x) -> Some (Z.of_string (Uint63.to_string x))
  | _ -> None

let cpp_string s =
  let b = Buffer.create (String.length s + 2) in
  Buffer.add_char b '"';
  String.iter
    (fun c ->
      match c with
      | '"' -> Buffer.add_string b "\\\""
      | '\\' -> Buffer.add_string b "\\\\"
      | '\n' -> Buffer.add_string b "\\n"
      | c when Char.code c < 0x20 || Char.code c >= 0x7f -> Buffer.add_string b (Printf.sprintf "\\%03o" (Char.code c))
      | c -> Buffer.add_char b c)
    s;
  Buffer.add_char b '"';
  Buffer.contents b

let structured r =
  if Base.Table.is_mapped_operation r then (Base.Mapping_operation.find r).Base.Mapping_operation.structured else None

let lowers r (values : expr list) =
  Option.has_some (structured r)
  && not (List.exists (function (Literal (String _ | Characters _) : expr) -> true | _ -> false) values)

let lower r ~(types : ty list) ~(yields : ty option) ~(values : expr list) : expr =
  let op = Base.Mapping_operation.find r in
  let body = Option.get op.structured in
  let values = Array.of_list values in
  let arg_type i = Stdlib.Option.join (List.nth_opt op.argument_types i) in
  let arg_literal i = if i < Array.length values then literal_value values.(i) else None in
  let fail d =
    CErrors.user_err Pp.(str "Crane: the operation mapping of" ++ spc () ++ Printer.pr_global r ++ str ":" ++ spc () ++ d)
  in
  let body = T.fold ~fail ~arg_type ~arg_literal body in
  let rec cpp_type : T.ty -> ty = function
    | Int t -> External (Cpp_ir.Integer_type.spelling t, [])
    | Bool -> External ("bool", [])
    | Float64 -> External ("double", [])
    | Result -> (
      match yields with
      | Some t -> t
      | None -> CErrors.anomaly Pp.(str "a structured operation names ResultType at a use with no type: " ++ GlobRef.print r) )
    | Plan e -> Base.Mapping_plan.instantiate e types
  and go (e : T.t) : expr =
    match e with
    | Arg i ->
      if i < Array.length values then values.(i)
      else CErrors.anomaly Pp.(str "a structured operation's argument is not supplied: " ++ GlobRef.print r)
    | Lit (t, v) -> Literal (Integer (t, v))
    | Bool_lit b -> Literal (Bool b)
    | String_lit s -> Foreign_text (cpp_string s)
    | Unop (o, a) -> Unary ((match o with Neg -> Negate | Not -> Not | Bit_not -> Bit_not), go a)
    | Binop (o, a, b) ->
      let o : Cpp_ir.Binary_operator.t =
        match o with
        | Add _ -> Add
        | Sub _ -> Subtract
        | Mul _ -> Multiply
        | Div -> Divide
        | Mod -> Modulo
        | Less -> Less
        | Less_eq -> Less_equal
        | Greater -> Greater
        | Greater_eq -> Greater_equal
        | Equal -> Equal
        | Not_equal -> Not_equal
        | And -> And
        | Or -> Or
        | Bit_and -> Bit_and
        | Bit_or -> Bit_or
        | Bit_xor -> Bit_xor
        | Shl -> Shift_left
        | Shr -> Shift_right
      in
      Binary (o, go a, go b)
    | Cond (c, a, b) -> Conditional (go c, go a, go b)
    | Convert (k, t, a) -> Integer_conversion (k, cpp_type t, go a)
    | Call (f, ts, args) -> Named_call (f, List.map cpp_type ts, List.map go args)
    (* A member read of a moved object moves the member, as
       {!Erasure.lower_access_moves}, which ran before, does. *)
    | Method (o, m, args) -> (
      match go o with
      | Move o -> Access_call (Dot, o, Id.of_string_soft m, List.map go args)
      | o -> Access_call (Dot, o, Id.of_string_soft m, List.map go args) )
    | Member (o, f) -> (
      match go o with
      | Move o -> Move (Access (Dot, o, Id.of_string_soft f))
      | o -> Access (Dot, o, Id.of_string_soft f) )
    | Index (o, i) -> ( match go o with Move o -> Index (o, go i) | o -> Index (o, go i) )
    | Build (t, args) -> Converting_construct (cpp_type t, List.map go args)
    | Enum_value (t, x) -> Type_member (cpp_type t, Id.of_string_soft x)
    | Verbatim s -> Foreign_text s
  in
  Mapped_operation (r, go body)
