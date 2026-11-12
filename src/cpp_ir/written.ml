(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What printing a term writes, asked of its structure rather than of its
    rendering: the variables a body's text reads, and whether an expression
    is written with a leading prefix pointer operator. *)

open Names
open Grammar

(** The identifiers written in [s], as whole tokens. *)
let identifiers_of_text s =
  let n = String.length s in
  let is_word c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') || c = '_' in
  let rec word_end j = if j < n && is_word s.[j] then word_end (j + 1) else j in
  let rec go i acc =
    if i >= n then acc
    else if is_word s.[i] then
      let j = word_end i in
      let w = String.sub s i (j - i) in
      go j (if Id.is_valid w then Id.of_string w :: acc else acc)
    else go (i + 1) acc
  in
  go 0 []

(** The template a custom match is written from: an owned scrutinee's
    structured binding binds by value. *)
let custom_match_text (m : 'p Custom_match.t) =
  match m.hold with
  | Owned when Foreign_template.structured_binding m.template <> None -> Foreign_template.bound_by_value m.template
  | Owned | Borrowed -> m.template

(* Whether an inline mapping, as printed, spells its value argument [i]: a
   callee is printed applied to all of them, a template spells exactly the
   [%a{i}] it names. *)
let inline_spells_arg (t : Foreign.template) =
  match t.form with
  | Bare_callee -> fun _ -> true
  | Templated | Block ->
    let tokens = Foreign_template.term_template t.text in
    fun i -> List.mem (Foreign_template.CCarg i) tokens

(** [vars] without the variables in [bound]. *)
let without bound vars = List.filter (fun v -> not (List.exists (Id.equal v) bound)) vars

(* What the [decltype]s in the types [visit] hands its argument read; a
   type constructor, of which only the head is written, is not entered. *)
let rec in_types : type p. ((p Type.t -> unit) -> unit) -> Id.t list =
 fun visit ->
  let acc = ref [] in
  let rec go (t : p Type.t) =
    match t with
    | Type_of e -> acc := expr e @ !acc
    | Type_constructor _ -> ()
    | t -> Children.type_children go t
  in
  visit go;
  !acc

(* The variables the text of [e] reads. *)
and expr : type p. p Expr.t -> Id.t list =
 fun e ->
  let types = in_types (fun f -> Children.expr {Children.expr = ignore; stmt = ignore; type_ = f} e) in
  types
  @
  match e with
  | Local id -> [id]
  | Foreign_text s -> identifiers_of_text s
  | Call (_, (Entity (_, _, Some {inline = Some t; _}) as f), args) ->
    let spells = inline_spells_arg t in
    expr f @ List.concat (List.mapi (fun i a -> if spells i then expr a else []) args)
  | Foreign (_, fr) -> List.concat (List.mapi (fun i a -> if List.mem (Foreign.Value i) fr.pieces then expr a else []) fr.values)
  | Lambda l -> without (List.filter_map snd l.params) (body l.body)
  | e ->
    let found = ref [] in
    Children.expr {Children.expr = (fun e -> found := !found @ expr e); stmt = (fun s -> found := !found @ stmt s); type_ = ignore} e;
    !found

(* The variables the text of [s] reads. *)
and stmt : type p. p Stmt.t -> Id.t list =
 fun s ->
  let types = in_types (fun f -> Children.stmt {Children.expr = ignore; stmt = ignore; type_ = f} s) in
  types
  @
  match s with
  | Return (Some e) | Expression e | Bind_variable (_, _, e) | Structured_binding (_, e) -> expr e
  | Return None -> []
  | Assign (l, r) -> expr l @ expr r
  | If {condition; then_; else_} -> expr condition @ body then_ @ body else_
  | If_constexpr {then_; else_; _} -> body then_ @ body else_
  | Foreign_text text | Assert (Checked text) -> identifiers_of_text text
  | Custom_match m ->
    let tokens = Foreign_template.match_template (custom_match_text m) in
    let spells token = List.mem token tokens in
    (if spells Foreign_template.CCscrut then expr m.scrutinee else [])
    @ List.concat
        (List.mapi
           (fun i (b : p Custom_match.branch) ->
             if spells (Foreign_template.CCbody i) then
               without (List.map (fun (p : p Custom_match.param) -> p.name) b.params) (body b.body)
             else [] )
           m.branches )
  | Switch {scrutinee; branches; default; _} ->
    expr scrutinee @ List.concat_map (fun (_, b) -> body b) branches @ Option.cata body [] default
  | Match (scrutinee, branches, default) ->
    expr scrutinee.expr
    @ List.concat_map
        (fun (br : p Match.branch) ->
          let bound =
            List.map (fun (f : p Match.field_binding) -> f.name) br.field_bindings @ Option.cata (fun v -> [v]) [] br.var
          in
          without bound (List.concat_map expr br.extra_conditions @ body br.body) )
        branches
    @ Option.cata body [] default
  | Block ss -> body ss
  | If_declaration {name; init; then_; else_; _} -> expr init @ without [name] (body then_) @ body else_
  | For_range (id, e, b) -> expr e @ without [id] (body b)
  | While (c, b) -> expr c @ body b
  | Declare _ | Throw _ | Assert (Stated _) | Comment _ | Local_struct _ | Local_type_alias _
  | Declare_value_initialized _ | Continue | Break ->
    []
  | Foreign_block b -> List.concat_map expr b.values

(* The variables the text of a statement list reads, excluding those a
   statement declares from the statements after it. *)
and body : type p. p Stmt.t list -> Id.t list =
 fun stmts ->
  let rec go defined = function
    | [] -> []
    | (s : p Stmt.t) :: rest ->
      let declared =
        match s with
        | Bind_variable (id, Declare _, _) | Declare (id, _, _) | Declare_value_initialized (id, _) -> [id]
        | Structured_binding (ids, _) -> ids
        | _ -> []
      in
      without defined (stmt s) @ go (declared @ defined) rest
  in
  go [] stmts

(** [reads_as_printed b id] is whether the text the statements [b] are
    printed as reads the variable [id]: a mapping's unspliced argument or
    branch does not reach the text, and foreign text, a checked precondition
    and a [decltype] in a type do. *)
let reads_as_printed b =
  let read = body b in
  fun id -> List.exists (Id.equal id) read

(* A conjunction under a disjunction, or the reverse, is parenthesised
   where it is written. *)
let parenthesised_operand (op : Binary_operator.t) (e : 'p Expr.t) =
  match e with
  | Binary (And, _, _) -> op = Or
  | Binary (Or, _, _) -> op = And
  | _ -> false

let starts_with_pointer_operator s = s <> "" && (s.[0] = '*' || s.[0] = '&')

(** Whether [e] is written with a leading prefix pointer operator, [*] or
    [&]. *)
let rec written_with_leading_pointer_operator : type p. p Expr.t -> bool = function
  | Dereference _ | Unary (Address_of, _) -> true
  | Foreign_text s -> starts_with_pointer_operator s
  | Numeral (_, n) -> starts_with_pointer_operator n.text
  | Binary (op, lhs, _) -> (not (parenthesised_operand op lhs)) && written_with_leading_pointer_operator lhs
  | Method_call m -> written_with_leading_pointer_operator m.receiver
  | Foreign ((Constant | Call), fr) -> foreign_written_with_leading_pointer_operator fr
  | _ -> false

(* A mapping's text begins with its first non-empty piece; a value spliced
   there begins as it is written, unless it is a string literal (written as
   the string object it stands for) or parenthesised for a member access
   following it. *)
and foreign_written_with_leading_pointer_operator : type p. p Foreign.t -> bool =
 fun fr ->
  let rec first : Foreign.piece list -> bool = function
    | Text "" :: rest -> first rest
    | Text s :: _ -> starts_with_pointer_operator s
    | Value i :: rest -> (
      let followed_by_dot =
        match rest with
        | Text s :: _ ->
          let s = String.trim s in
          s <> "" && s.[0] = '.'
        | _ -> false
      in
      match List.nth_opt fr.values i with
      | Some (Literal (String _)) | None -> false
      | Some e when followed_by_dot && spliced_in_parentheses e -> false
      | Some e -> written_with_leading_pointer_operator e )
    | _ -> false
  in
  first fr.pieces

(** Whether a mapping's text parenthesises [e] where a member access
    follows it. *)
and spliced_in_parentheses : type p. p Expr.t -> bool = function
  | Binary _ | Foreign ((Call | Block_value _), _) | Call (_, Foreign _, _) -> true
  | e -> written_with_leading_pointer_operator e
