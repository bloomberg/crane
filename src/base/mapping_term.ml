(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** See [mapping_term.mli]. *)

open Mapping_descriptor
module It = Cpp_ir.Integer_type

type ty = Int of It.t | Bool | Float64 | Result | Plan of Mapping_plan.type_expr

type t =
  | Arg of int
  | Lit of It.t * Z.t
  | Bool_lit of bool
  | String_lit of string
  | Unop of Cpp.unop * t
  | Binop of Cpp.binop * t * t
  | Cond of t * t * t
  | Convert of Cpp.conversion * ty * t
  | Call of string * ty list * t list
  | Method of t * string * t list
  | Member of t * string
  | Index of t * t
  | Build of ty * t list
  | Enum_value of ty * string
  | Verbatim of string

(* {1 Types} *)

let promote (t : It.t) : It.t = match t with I8 | I16 | U8 | U16 | Char | Uchar -> I32 | t -> t

(* The type of [a op b] for promoted [a], [b], where every platform agrees
   on it: [std::size_t] meets only itself, as it is [unsigned long] where
   [uint64_t] is [unsigned long long]. *)
let common (a : It.t) (b : It.t) : It.t option =
  if a = b then Some a
  else
    let rank : It.t -> int option = function I32 | U32 -> Some 1 | I64 | U64 -> Some 2 | _ -> None in
    match (rank a, rank b, It.signed a, It.signed b) with
    | Some ra, Some rb, Some sa, Some sb ->
      if sa = sb then Some (if ra >= rb then a else b)
      else
        let (u, ru), (s, rs) = if sa then ((b, rb), (a, ra)) else ((a, ra), (b, rb)) in
        if ru >= rs then Some u else Some s
    | _ -> None

let rec type_of ~(arg_type : int -> It.t option) (e : t) : It.t option =
  let ty = type_of ~arg_type in
  match e with
  | Arg i -> arg_type i
  | Lit (t, _) -> Some t
  | Unop ((Neg | Bit_not), e) -> Option.map promote (ty e)
  | Binop ((Add _ | Sub _ | Mul _ | Div | Mod | Bit_and | Bit_or | Bit_xor), a, b) -> (
    match (ty a, ty b) with Some a, Some b -> common (promote a) (promote b) | _ -> None )
  | Binop ((Shl | Shr), a, _) -> Option.map promote (ty a)
  | Cond (_, a, b) -> ( match (ty a, ty b) with Some a, Some b when a = b -> Some a | _ -> None )
  | Convert (_, Int t, _) -> Some t
  | _ -> None

(* {1 Resolution} *)

let unsigned_of (t : It.t) : It.t = match t with I64 | U64 -> U64 | Size -> Size | _ -> U32

(* [fail] raises the mapping's error. *)
let failing fail fmt =
  Printf.ksprintf
    (fun s ->
      fail (Pp.strbrk s);
      assert false)
    fmt

let resolve ~fail ~arg ~ty ~arg_type ~result_type (body : Cpp.term) : t =
  let failf fmt = failing fail fmt in
  let rec go env (e : Cpp.term) : t =
    let go' = go env in
    match e with
    | Arg x -> Arg (arg x)
    | Int_lit (t, v) ->
      if not (It.fits t v) then failf "operation_cpp writes the literal %s, which is not a %s." (Z.to_string v) (It.spelling t);
      Lit (t, v)
    | Bool_lit b -> Bool_lit b
    | String_lit s -> String_lit s
    | Unop (o, e) -> Unop (o, go' e)
    | Binop (((Add o | Sub o | Mul o) as op), a, b) when o <> Unchecked -> (
      let a = go' a and b = go' b in
      let plain : Cpp.binop = match op with Add _ -> Add Unchecked | Sub _ -> Sub Unchecked | _ -> Mul Unchecked in
      match o with
      | Wrapping -> (
        match (type_of ~arg_type a, type_of ~arg_type b) with
        | Some ta, Some tb when ta = tb -> (
          match (ta, It.signed ta) with
          | (U32 | U64 | Size), _ -> Binop (plain, a, b)
          | _, Some _ ->
            let u = Int (unsigned_of ta) in
            Convert (Wrap, Int ta, Binop (plain, Convert (Wrap, u, a), Convert (Wrap, u, b)))
          | _, None -> failf "operation_cpp wraps an operation on char, whose signedness is the platform's." )
        | _ ->
          failf
            "operation_cpp applies a Wrapping operator to operands whose integer types Crane does not know \
             to be one type; write the conversions, or map the arguments' types to Int." )
      | Saturating ->
        let f = match op with Add _ -> "std::add_sat" | Sub _ -> "std::sub_sat" | _ -> "std::mul_sat" in
        Call (f, [], [a; b])
      | Unchecked -> Binop (op, a, b) )
    | Binop (o, a, b) ->
      let a = go' a in
      Binop (o, a, go' b)
    | Cond (c, a, b) ->
      let c = go' c in
      let a = go' a in
      Cond (c, a, go' b)
    | Convert (k, target, e) ->
      let t =
        match (k, target) with
        | (Exact | Wrap | Saturate), Int t -> Int t
        | (Exact | Wrap | Saturate), Result_type -> (
          match result_type with
          | Some t -> Int t
          (* Not known to be an integer type: converted as written, never
             folded. *)
          | None -> Result )
        | (Exact | Wrap | Saturate), _ ->
          failf "operation_cpp converts with Exact, Wrap or Saturate to a type that is not an Int; use Build."
        | To_enum, _ -> ty target
      in
      Convert (k, t, go' e)
    | Call (f, ts, args) -> Call (f, List.map ty ts, List.map go' args)
    | Method (e, m, args) ->
      let e = go' e in
      Method (e, m, List.map go' args)
    | Member (e, f) -> Member (go' e, f)
    | Index (e, i) ->
      let e = go' e in
      Index (e, go' i)
    | Build (t, args) -> Build (ty t, List.map go' args)
    | Enum_value (t, x) -> Enum_value (ty t, x)
    | Let_in (x, v, b) -> go ((x, go' v) :: env) b
    | Var x -> (
      match List.assoc_opt x env with Some v -> v | None -> failf "operation_cpp names Var %s, which no LetIn binds." x )
    | Verbatim s -> Verbatim s
  in
  go [] body

(* {1 Folding} *)

let rec fold ~fail ~arg_type ?(arg_literal = fun _ -> None) (e : t) : t =
  let fold = fold ~fail ~arg_type ~arg_literal in
  let literal (e : t) =
    match e with
    | Lit (t, v) -> Some (t, v)
    | Arg i -> (
      match (arg_type i, arg_literal i) with Some t, Some v when It.fits t v -> Some (t, v) | _ -> None )
    | _ -> None
  in
  match e with
  | Convert (k, target, inner) -> (
    let inner = fold inner in
    (* R3: an Exact conversion to a type holding every value of its
       operand's type, under another conversion, converts nothing. *)
    let rec strip (inner : t) =
      match inner with
      | Convert (Exact, Int b, e') -> (
        match type_of ~arg_type e' with Some te when It.includes b te -> strip e' | _ -> inner )
      | _ -> inner
    in
    let inner = match k with To_enum -> inner | _ -> strip inner in
    match (target, literal inner) with
    (* R1: a literal converted is a literal of the target type. *)
    | Int t', Some (_, v) -> (
      match k with
      | Exact ->
        if It.fits t' v then Lit (t', v)
        else
          failing fail "operation_cpp converts the literal %s with Exact to %s, which does not hold it."
            (Z.to_string v) (It.spelling t')
      | Wrap -> ( match It.wrap t' v with Some v' -> Lit (t', v') | None -> Convert (k, target, inner) )
      | Saturate -> Lit (t', It.saturate t' v)
      | To_enum -> Convert (k, target, inner) )
    (* R2: a conversion to the type its operand has is its operand. *)
    | Int t', None when k <> To_enum && type_of ~arg_type inner = Some t' -> inner
    | _ -> Convert (k, target, inner) )
  | Arg _ | Lit _ | Bool_lit _ | String_lit _ | Verbatim _ | Enum_value _ -> e
  | Unop (o, a) -> Unop (o, fold a)
  | Binop (o, a, b) ->
    let a = fold a in
    Binop (o, a, fold b)
  | Cond (c, a, b) ->
    let c = fold c in
    let a = fold a in
    Cond (c, a, fold b)
  | Call (f, ts, args) -> Call (f, ts, List.map fold args)
  | Method (r, m, args) ->
    let r = fold r in
    Method (r, m, List.map fold args)
  | Member (r, f) -> Member (fold r, f)
  | Index (r, i) ->
    let r = fold r in
    Index (r, fold i)
  | Build (t, args) -> Build (t, List.map fold args)

(* {1 Text} *)

let type_text = function
  | Int t -> It.spelling t
  | Bool -> "bool"
  | Float64 -> "double"
  | Result -> "%ret"
  | Plan e -> Mapping_plan.text_of_type_expr e

let binop_text : Cpp.binop -> string = function
  | Add _ -> "+"
  | Sub _ -> "-"
  | Mul _ -> "*"
  | Div -> "/"
  | Mod -> "%"
  | Less -> "<"
  | Less_eq -> "<="
  | Greater -> ">"
  | Greater_eq -> ">="
  | Equal -> "=="
  | Not_equal -> "!="
  | And -> "&&"
  | Or -> "||"
  | Bit_and -> "&"
  | Bit_or -> "|"
  | Bit_xor -> "^"
  | Shl -> "<<"
  | Shr -> ">>"

let binop_precedence : Cpp.binop -> int = function
  | Mul _ | Div | Mod -> 13
  | Add _ | Sub _ -> 12
  | Shl | Shr -> 11
  | Less | Less_eq | Greater | Greater_eq -> 9
  | Equal | Not_equal -> 8
  | Bit_and -> 7
  | Bit_xor -> 6
  | Bit_or -> 5
  | And -> 4
  | Or -> 3

let rec text (e : t) : string =
  let list es = String.concat ", " (List.map text es) in
  let types ts = match ts with [] -> "" | _ -> "<" ^ String.concat ", " (List.map type_text ts) ^ ">" in
  match e with
  | Arg i -> Printf.sprintf "%%a%d" i
  | Lit (t, v) -> if Z.sign v < 0 then "(" ^ It.spell_literal t v ^ ")" else It.spell_literal t v
  | Bool_lit b -> if b then "true" else "false"
  | String_lit s -> "\"" ^ String.escaped s ^ "\""
  | Unop (o, a) -> "(" ^ (match o with Neg -> "-" | Not -> "!" | Bit_not -> "~") ^ text a ^ ")"
  | Binop (o, a, b) -> "(" ^ operand o ~right:false a ^ " " ^ binop_text o ^ " " ^ operand o ~right:true b ^ ")"
  | Cond (c, a, b) -> "(" ^ text c ^ " ? " ^ text a ^ " : " ^ text b ^ ")"
  | Convert (k, t, a) -> Cpp_ir.Integer_conversion.cast k ^ "<" ^ type_text t ^ ">(" ^ text a ^ ")"
  | Call (f, ts, args) -> f ^ types ts ^ "(" ^ list args ^ ")"
  | Method (r, m, args) -> receiver r ^ "." ^ m ^ "(" ^ list args ^ ")"
  | Member (r, f) -> receiver r ^ "." ^ f
  | Index (r, i) -> receiver r ^ "[" ^ text i ^ "]"
  | Build (t, args) -> type_text t ^ "(" ^ list args ^ ")"
  | Enum_value (t, x) -> type_text t ^ "::" ^ x
  | Verbatim s -> s

(* An operand of [o], parenthesised (by [text]) unless it is an operator
   binding tighter than [o], or as tight on the left. *)
and operand o ~right e =
  match e with
  | Binop (o', a, b) ->
    let p = binop_precedence o and p' = binop_precedence o' in
    if p' > p || (p' = p && not right) then operand o' ~right:false a ^ " " ^ binop_text o' ^ " " ^ operand o' ~right:true b
    else text e
  | _ -> text e

(* An argument's hole is parenthesised where a member access follows it
   ({!Cpp_ir.Written.spliced_in_parentheses}). *)
and receiver = function
  | Arg i -> Printf.sprintf "%%a%d" i
  | (Unop _ | Binop _ | Cond _ | Convert _ | Call _ | Method _ | Member _ | Index _ | Build _ | Enum_value _) as e ->
    text e
  | e -> "(" ^ text e ^ ")"

(* The text of a whole body: a template is spliced as an operand of the
   lowest precedence, so its outermost operator needs no parentheses. *)
let text e =
  match e with
  | Binop (o, a, b) -> operand o ~right:false a ^ " " ^ binop_text o ^ " " ^ operand o ~right:true b
  | e -> text e
