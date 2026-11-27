(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The declared view conversions at calls.  See [view_args.mli]. *)

open Names
module Plan = Base.Mapping_plan
module Op = Base.Mapping_operation

type expr = Cpp_ir.Lowered.Expr.t
type stmt = Cpp_ir.Lowered.Stmt.t
type ty = Cpp_ir.Lowered.Type.t

(* What a caller's expression holds, as far as views go. *)
type held =
  | Canonical of GlobRef.t * ty list  (** a value of the mapped head at its type arguments *)
  | View of Plan.view_kind * GlobRef.t * ty list  (** a view parameter of the mapped head *)
  | Borrowed of Op.view_conversions * ty list
      (** a view an operation returned borrowed, with the call's type
          arguments its conversions are written over *)
  | Unknown

(* A conversion: a term template of [%a0] over [types], of the mapped head
   or operation [custom]. *)
type conversion = { custom : GlobRef.t; text : string; types : ty list }

(* Where a call takes a view: an operation's argument, whose conversions
   are in the operation's vocabulary over the call's type arguments, or a
   generated function's parameter, whose are the mapping's over the
   argument's own type arguments. *)
type target =
  | Op_view of GlobRef.t * Op.view_conversions * ty list
  | Plan_view of Plan.view_kind * GlobRef.t

let target_kind = function Op_view (_, c, _) -> c.kind | Plan_view (k, _) -> k

let target_mapped = function Op_view (_, c, _) -> c.mapped | Plan_view (_, g) -> g

let fail detail = CErrors.user_err Pp.(hov 0 (str "Crane: " ++ detail))

let kind_name = function Plan.Read_view -> "read view" | Plan.Write_view -> "writable view"

let pieces text : Cpp_ir.Foreign.piece list =
  List.map
    (function
      | Cpp_ir.Foreign_template.Text s -> Cpp_ir.Foreign.Text s
      | Ty_arg i | Elem i -> Type_argument i
      | Arg i -> Value i
      | Ret -> Yields
      | Result -> Result
      | Scrut | Ty | Body _ | Br_var _ | Br_var_ty _ ->
        CErrors.anomaly (Pp.str "View_args: a match template's hole in a view conversion."))
    (Cpp_ir.Foreign_template.term_template text)

let apply (c : conversion) (e : expr) : expr =
  Foreign (Call, {custom = c.custom; types = c.types; values = [e]; yields = None; pieces = pieces c.text})

let names_type_arguments text =
  List.exists
    (function Cpp_ir.Foreign_template.Ty_arg _ | Elem _ -> true | _ -> false)
    (Cpp_ir.Foreign_template.term_template text)

(* The mapped head and type arguments a declared type names, under the
   declarators a parameter adds. *)
let rec mapped_type (t : ty) =
  match t with
  | Reference (_, t) | Const t | In_namespace (_, t) -> mapped_type t
  | Entity_application (r, tys, _) when Plan.is_type_head r -> Some (r, tys)
  | _ -> None

let view_kind : Cpp_ir.Param_mode.view -> Plan.view_kind = function
  | Read_view -> Plan.Read_view
  | Write_view -> Plan.Write_view

(* The view an operation call returns borrowed, if it is one. *)
let borrowed_call (e : expr) =
  match e with
  | Call (_, Entity (r, tys, Some {inline = Some _; _}), _) when Base.Table.is_mapped_operation r -> (
    match (Op.find r).result_view with Some c -> Some (c, tys) | None -> None )
  | _ -> None

let plan_view g k =
  match Plan.view (Plan.find g) k with
  | Some v -> v
  | None -> CErrors.anomaly Pp.(str "View_args: a view the typed mapping does not declare.")

(** The parameter modes of the local lambdas a body binds, by the variable
    each is bound to: what a direct call of one takes, as {!targets} reads
    it.  A name bound to more than one lambda is left out. *)
type locals = (Id.t * Cpp_ir.Param_mode.t) list option Id.Map.t

(* The positions a call of [f] with [n] arguments takes views at; a call of
   a local lambda, as [locals] records its parameters. *)
let targets ?(locals : locals = Id.Map.empty) (u : Unit_plan.Context.t) (f : expr) n : int -> target option =
  match f with
  | Local x -> (
    match Id.Map.find_opt x locals with
    | Some (Some modes) when List.length modes = n ->
      fun i ->
        Option.bind (List.nth_opt modes i) (fun ((_, m) : _ * Cpp_ir.Param_mode.t) ->
            match m.form with By_view (k, g) -> Some (Plan_view (view_kind k, g)) | _ -> None)
    | _ -> fun _ -> None )
  | Entity (r, tys, Some {inline = Some _; _}) when Base.Table.is_mapped_operation r ->
    let op = Op.find r in
    fun i ->
      List.find_map
        (fun (a : Op.argument) ->
          if a.position = i then Option.map (fun c -> Op_view (r, c, tys)) a.view else None)
        op.arguments
  | Entity (r, _, _) when not (Base.Table.is_custom r) -> (
    match Option.bind (Core_plan.Callable_abi.lookup u.callables r) Core_plan.Callable_abi.modes with
    | Some modes when List.length modes = n ->
      fun i ->
        Option.bind (List.nth_opt modes i) (fun (m : Cpp_ir.Param_mode.t) ->
            match m.form with By_view (k, g) -> Some (Plan_view (view_kind k, g)) | _ -> None)
    | _ -> fun _ -> None )
  | _ -> fun _ -> None

(* Whether a call of [f] with [n] arguments may invalidate a view of its
   argument [i]. *)
let invalidating (u : Unit_plan.Context.t) (f : expr) n i =
  match f with
  | Entity (r, _, Some {inline = Some _; _}) when Base.Table.is_mapped_operation r ->
    let op = Op.find r in
    List.exists
      (fun (a : Op.argument) ->
        a.position = i
        && ( a.use = Base.Mapping_descriptor.Replace
           || a.use = Base.Mapping_descriptor.Opaque_use
           || List.exists
                (function Base.Mapping_descriptor.Invalidates_views p -> p.path_argument = a.name | _ -> false)
                op.facts ))
      op.arguments
  | Entity (r, _, _) when not (Base.Table.is_custom r) -> (
    match Option.bind (Core_plan.Callable_abi.lookup u.callables r) Core_plan.Callable_abi.modes with
    | Some modes when List.length modes = n -> (
      match List.nth_opt modes i with Some m -> m.invalidates_views | None -> false )
    | _ -> false )
  | _ -> false

let callee_name (f : expr) =
  match f with Entity (r, _, _) -> Printer.pr_global r | _ -> Pp.str "a callee"

(* The variables a function's [params] (recorded [modes]) and [body]
   declare, and what each holds. *)
let declared_holdings params modes body =
  let held = ref Id.Map.empty in
  let conflict = ref Id.Set.empty in
  let note x h =
    match Id.Map.find_opt x !held with
    | Some h' when h' != h -> conflict := Id.Set.add x !conflict
    | _ -> held := Id.Map.add x h !held
  in
  List.iter
    (fun (x, t) ->
      match List.assoc_opt x modes with
      | Some ({form = By_view (k, g); _} : Cpp_ir.Param_mode.t) -> (
        let k = view_kind k in
        match Plan.view_arguments (Plan.find g) k t with
        | Some tys -> note x (View (k, g, tys))
        | None -> note x Unknown )
      | _ -> ( match mapped_type t with Some (r, tys) -> note x (Canonical (r, tys)) | None -> note x Unknown ))
    params;
  let rec fs (s : stmt) =
    ( match s with
    | Bind_variable (x, Declare (t, _), init) -> (
      match (mapped_type t, t, borrowed_call init, init) with
      | Some (r, tys), _, _, _ -> note x (Canonical (r, tys))
      | None, Auto, Some (c, tys), _ -> note x (Borrowed (c, tys))
      | None, Auto, None, Call ({yields = Typed yt; _}, _, _) -> (
        match mapped_type yt with Some (r, tys) -> note x (Canonical (r, tys)) | None -> note x Unknown )
      | _ -> note x Unknown )
    | Bind_variable (x, Declare_deduced (v, _), init) -> (
      match (borrowed_call init, v) with
      | Some (c, tys), _ -> note x (Borrowed (c, tys))
      | None, Typed yt -> (
        match mapped_type yt with Some (r, tys) -> note x (Canonical (r, tys)) | None -> note x Unknown )
      | _ -> note x Unknown )
    | Declare (x, t, _) | Declare_value_initialized (x, t) -> (
      match mapped_type t with Some (r, tys) -> note x (Canonical (r, tys)) | None -> note x Unknown )
    | _ -> () );
    Cpp_ir.Map.stmt (rw ()) s
  and fe (e : expr) =
    ( match e with
    | Lambda l ->
      (* A local lambda's parameter {!local_view_params} made a view holds
         the view; any other holds what nothing here says. *)
      List.iter
        (fun (t, x) ->
          Option.iter
            (fun x ->
              match List.assoc_opt x l.modes with
              | Some ({form = By_view (k, g); _} : Cpp_ir.Param_mode.t) -> (
                let k = view_kind k in
                match Plan.view_arguments (Plan.find g) k t with
                | Some tys -> note x (View (k, g, tys))
                | None -> note x Unknown )
              | _ -> note x Unknown)
            x)
        l.params
    | _ -> () );
    Cpp_ir.Map.expr (rw ()) e
  and rw () = Cpp_ir.Map.make ~expr:fe ~stmt:fs ~type_:Fun.id () in
  List.iter (fun s -> ignore (fs s)) body;
  Id.Set.fold (fun x m -> Id.Map.add x Unknown m) !conflict !held

(* The type arguments of [p]'s canonical type, read back from the value
   [e] with [crane::template_argument_t] (theories/cpp/obj.h):
   each is reached from [decltype(e)] through the class template arguments,
   pointees and [const]s the canonical type names it under. *)
let read_back (p : Plan.t) (e : expr) : ty list =
  let rec paths (t : Plan.type_expr) =
    match t with
    | Parameter i | Boxed (i, _) -> [(i, [])]
    | Apply (_, args) ->
      List.concat
        (List.mapi
           (fun j a ->
             match a with
             | Plan.Type a -> List.map (fun (i, path) -> (i, `Argument j :: path)) (paths a)
             | Plan.Value _ -> [])
           args)
    | Pointer t -> List.map (fun (i, path) -> (i, `Pointee :: path)) (paths t)
    | Const t -> paths t
    | Name _ | Verbatim _ -> []
  in
  let found = paths p.canonical in
  let n = List.fold_left (fun n (i, _) -> max n (i + 1)) 0 found in
  let at path : ty =
    List.fold_left
      (fun (t : ty) -> function
        | `Argument j -> External ("crane::template_argument_t", [t; External (string_of_int j, [])])
        | `Pointee -> External ("std::remove_pointer_t", [External ("std::remove_cvref_t", [t])]))
      (Type_of e) path
  in
  List.init n (fun i -> match List.assoc_opt i found with Some path -> at path | None -> Any)

(* A string literal taken as the read view [t]: the view of the literal's
   characters, constructed from them, and from their count where they hold
   a NUL (a view of a character array would stop at it).  A literal has
   static storage, so the view needs no owner and no canonical string is
   made for it.  The read view of a type with literals is therefore
   constructible from a literal and a count (Descriptor.v, [ViewSpec]); one
   whose type names a type argument is left to its conversion. *)
let literal_view t (e : expr) : expr option =
  match e with
  | Literal (String s) when target_kind t = Plan.Read_view -> (
    let rec closed : Plan.type_expr -> bool = function
      | Parameter _ | Boxed _ -> false
      | Name _ | Verbatim _ -> true
      | Pointer t | Const t -> closed t
      | Apply (_, args) -> List.for_all (function Plan.Type t -> closed t | Plan.Value _ -> true) args
    in
    match Plan.view (Plan.find (target_mapped t)) Plan.Read_view with
    | Some v when closed v.view_type ->
      let text = Pstring.to_string s in
      let count : expr list = if String.contains text '\000' then [Literal (Int (String.length text))] else [] in
      Some (Converting_construct (Plan.instantiate v.view_type [], Literal (Characters s) :: count))
    | _ -> None )
  | _ -> None

let materialisable g =
  match Plan.view (Plan.find g) Plan.Read_view with
  | Some {escape = Materialise text; _} -> Some (fun types e -> apply {custom = g; text; types} e)
  | Some {escape = Borrow_only; _} | None -> None

(* Whether the template [text] places its argument [%a0] more than once. *)
let repeats_argument text = Cpp_ir.Foreign_template.arg_mentions text 0 > 1

(* Whether evaluating [e] again costs nothing and changes nothing. *)
let free_to_repeat (e : expr) = match e with Local _ | Entity (_, _, None) -> true | _ -> false

(** {1 Views at local lambdas}

    A local lambda -- [auto f = [..](params) { body };] -- only ever called
    directly, outside every lambda, takes a parameter of a mapped type that
    declares views by the view, when [body] uses the parameter only as an
    argument taken by a view: of the writable kind where one such use
    writes, of the read kind otherwise.  Its calls then pass the view of
    what they pass, converted as at any call taking one ({!targets} reads
    the lambda's modes), and a mapped identity passed so is used only
    through its views, where it was created: {!Local_storage} may keep it
    in a local.  A lambda named as a value, or a parameter used any other
    way -- returned, stored, captured, passed as the canonical value -- is
    left as it is: the view is borrow-only and would outlive its owner. *)

(* The argument lists of the calls [stmts] make of [f], when every
   occurrence of [f] in them is the callee of a call, outside every lambda,
   whose arguments do not name [f]; [None] otherwise. *)
let direct_calls f (stmts : stmt list) =
  let mentions (e : expr) = Cpp_ir.Variables.mem f (Cpp_ir.Variables.free_in_expr e) in
  let ok = ref true and found = ref false in
  let rec v : Cpp_ir.Lowered.phase Cpp_ir.Children.visitor =
    {expr = (fun e -> fe e); stmt = (fun s -> Cpp_ir.Children.stmt v s); type_ = ignore}
  and fe (e : expr) =
    match e with
    | Call (_, Local f', args) when Id.equal f f' ->
      found := true;
      if List.exists mentions args then ok := false
    | Local f' when Id.equal f f' -> ok := false
    | Lambda _ -> if mentions e then ok := false
    | _ -> Cpp_ir.Children.expr v e
  in
  List.iter (Cpp_ir.Children.stmt v) stmts;
  !ok && !found

(* The kinds of view the uses of [p] in [body] take, each an argument
   [targets] finds taken by a view of [g]; [None] when some use is not. *)
let view_uses u g p (body : stmt list) =
  let kinds = ref [] and ok = ref true in
  let is_p (a : expr) = match a with Local x | Move (Local x) -> Id.equal x p | _ -> false in
  let rec v : Cpp_ir.Lowered.phase Cpp_ir.Children.visitor =
    {expr = (fun e -> fe e); stmt = (fun s -> Cpp_ir.Children.stmt v s); type_ = ignore}
  and fe (e : expr) =
    match e with
    | Call (_, f, args) ->
      let target = targets u f (List.length args) in
      List.iteri
        (fun i a ->
          if is_p a then
            match target i with
            | Some t when GlobRef.CanOrd.equal (target_mapped t) g -> kinds := target_kind t :: !kinds
            | _ -> ok := false
          else fe a)
        args;
      fe f
    | Local x when Id.equal x p -> ok := false
    | Lambda _ when Cpp_ir.Variables.mem p (Cpp_ir.Variables.free_in_expr e) -> ok := false
    | _ -> Cpp_ir.Children.expr v e
  in
  List.iter (Cpp_ir.Children.stmt v) body;
  if !ok then Some !kinds else None

(* [l] with each parameter the section above admits taken by its view.
   What a variable holds is read by its name ({!declared_holdings}), so a
   parameter made a view is renamed to a name [taken] does not hold -- a
   variable of the enclosing body of the same name holds the canonical
   value. *)
let view_params u taken (l : Cpp_ir.Lowered.phase Cpp_ir.Expr.Lambda.t) =
  let taken = ref taken in
  let fresh p =
    let rec go i =
      let x = Id.of_string (Printf.sprintf "%s_view%s" (Id.to_string p) (if i = 0 then "" else string_of_int i)) in
      if Cpp_ir.Variables.mem x !taken then go (i + 1) else x
    in
    let x = go 0 in
    taken := x :: !taken;
    x
  in
  let declared = Cpp_ir.Variables.declared l.body in
  let param (t, x) =
    match (x, mapped_type t) with
    | Some p, Some (g, tys)
      when (not (List.mem_assoc p l.modes && Option.has_some (Cpp_ir.Param_mode.view (List.assoc p l.modes))))
           && not (Cpp_ir.Variables.mem p declared) -> (
      let plan = Plan.find g in
      match view_uses u g p l.body with
      | Some (_ :: _ as kinds) ->
        let k = if List.mem Plan.Write_view kinds then Plan.Write_view else Plan.Read_view in
        if Plan.has_view plan k then
          let mode : Cpp_ir.Param_mode.view = match k with Plan.Read_view -> Read_view | Plan.Write_view -> Write_view in
          let p' = fresh p in
          Some (p, ((Plan.view_type plan k tys, Some p'), (p', Cpp_ir.Param_mode.make Borrowed (By_view (mode, g)))))
        else None
      | _ -> None )
    | _ -> None
  in
  let changed = List.map param l.params in
  if List.for_all (fun c -> c = None) changed then l
  else
    let renamed = List.filter_map (Option.map (fun (p, (_, (p', _))) -> (p, p'))) changed in
    let rename x = match List.assoc_opt x renamed with Some y -> y | None -> x in
    let rec fe (e : expr) : expr =
      match e with Local x -> Local (rename x) | _ -> Cpp_ir.Map.expr (rw ()) e
    and fs (s : stmt) : stmt = Cpp_ir.Map.stmt (rw ()) s
    and rw () = Cpp_ir.Map.make ~expr:fe ~stmt:fs ~type_:Fun.id () in
    let params = List.map2 (fun c p -> match c with Some (_, (p', _)) -> p' | None -> p) changed l.params in
    let modes =
      List.fold_left
        (fun ms c -> match c with Some (p, (_, (p', m))) -> (p', m) :: List.remove_assoc p ms | None -> ms)
        l.modes changed
    in
    let binders = List.map (fun (x, b) -> (rename x, b)) l.binders in
    {l with params; modes; binders; body = List.map fs l.body}

(* [body] with every local lambda only called directly taking its
   parameters by view where {!view_params} admits them. *)
let local_view_params u params (body : stmt list) : stmt list =
  let taken = List.map fst params @ Cpp_ir.Variables.declared body @ Cpp_ir.Variables.free_in_body body in
  let rec stmts (ss : stmt list) : stmt list =
    match ss with
    | [] -> []
    | Bind_variable (f, tgt, Lambda l) :: rest when l.type_params = [] && direct_calls f rest ->
      let rest = stmts rest in
      Bind_variable (f, tgt, Cpp_ir.Map.expr (rw ()) (Lambda (view_params u taken l))) :: rest
    | s :: rest ->
      let s = fs s in
      s :: stmts rest
  and fs (s : stmt) : stmt = Cpp_ir.Map.stmt (rw ()) s
  and fe (e : expr) : expr = Cpp_ir.Map.expr (rw ()) e
  and rw () = Cpp_ir.Map.make ~stmts ~expr:fe ~stmt:fs ~type_:Fun.id () in
  stmts body

(* The modes of the parameters of each local lambda [body] binds
   ({!locals}). *)
let local_lambdas (body : stmt list) : locals =
  let table = ref Id.Map.empty in
  let rec v : Cpp_ir.Lowered.phase Cpp_ir.Children.visitor =
    {expr = (fun e -> Cpp_ir.Children.expr v e); stmt = (fun s -> fs s); type_ = ignore}
  and fs (s : stmt) =
    ( match s with
    | Bind_variable (f, _, Lambda l) ->
      let modes =
        List.map
          (fun (_, x) ->
            match x with
            | Some x -> (x, Option.default Cpp_ir.Param_mode.copied (List.assoc_opt x l.modes))
            | None -> (Id.of_string "_", Cpp_ir.Param_mode.copied))
          l.params
      in
      table := Id.Map.update f (function None -> Some (Some modes) | Some _ -> Some None) !table
    | _ -> () );
    Cpp_ir.Children.stmt v s
  in
  List.iter fs body;
  !table

let transform_body u params modes (body : stmt list) : stmt list =
  let body = local_view_params u params body in
  let locals = local_lambdas body in
  let targets = targets ~locals in
  let held = declared_holdings params modes body in
  (* What a statement needs bound ahead of it, innermost statement first:
     a value a conversion places more than once, or a copy a view is taken
     of.  Only where the statement evaluates its expressions once ([while]
     conditions do not). *)
  let pending : stmt list ref = ref [] in
  let hoisting = ref true in
  let counter = ref 0 in
  let rec fresh () =
    incr counter;
    let x = Id.of_string (Printf.sprintf "_view%d" !counter) in
    if Id.Map.mem x held then fresh () else x
  in
  let hoist (e : expr) : expr option =
    if not !hoisting then None
    else
      let x = fresh () in
      pending := Cpp_ir.Typed.bind_deduced x (e) :: !pending;
      Some (Local x)
  in
  (* [c] applied to [e], evaluated once. *)
  let apply_once (c : conversion) (e : expr) : expr =
    if repeats_argument c.text && not (free_to_repeat e) then
      match hoist e with Some x -> apply c x | None -> apply c e
    else apply c e
  in
  let holding x = match Id.Map.find_opt x held with Some h -> h | None -> Unknown in
  let is_view = function View _ -> true | Canonical _ | Borrowed _ | Unknown -> false in
  let is_canonical = function Canonical _ -> true | View _ | Borrowed _ | Unknown -> false in
  let holding_of (e : expr) =
    match e with
    | Local x -> holding x
    | _ -> (
      match borrowed_call e with
      | Some (c, tys) -> Borrowed (c, tys)
      | None -> (
        match e with
        | Call ({yields = Typed t; _}, _, _) -> (
          match mapped_type t with Some (r, tys) -> Canonical (r, tys) | None -> Unknown )
        | _ -> Unknown ) )
  in
  (* The canonical value copied out of the view [e] holds, as its mapping
     materialises it. *)
  let materialised what (h : held) (e : expr) : expr =
    let refuse g =
      fail
        Pp.(
          strbrk ("a " ^ what ^ " of") ++ spc () ++ Printer.pr_global g ++ spc ()
          ++ strbrk
               "escapes its owner (it is returned, stored, or passed where the \
                canonical value is taken), but the view is BorrowOnly: copying \
                it would not be the same value.  Keep the view within its \
                owner's lifetime, or declare MaterialiseView.")
    in
    match h with
    | Borrowed (c, tys) -> (
      match c.materialise with
      | Some text -> apply_once {custom = c.mapped; text; types = tys} e
      | None -> refuse c.mapped )
    | View (k, g, tys) -> (
      match (plan_view g k).escape with
      | Materialise text -> apply_once {custom = g; text; types = tys} e
      | Borrow_only -> refuse g )
    | Canonical _ | Unknown -> e
  in
  (* [e], which holds [h], narrowed to a view of kind [k] the target [t]
     takes, or [None] when it is no view.  A writable view is an operation's
     read view as it is: the operation's text reads through it, and C++
     converts it wherever the text spells the read view's type
     ([std::span<T>] to [std::span<const T>]).  A generated function's
     parameter is narrowed to: its element type may be deduced from the read
     view's own. *)
  let as_view f t (h : held) (e : expr) : expr option =
    let k = target_kind t in
    let narrowed have conv =
      if have = k then Some e
      else if have = Plan.Write_view && (match t with Op_view _ -> true | Plan_view _ -> false) then Some e
      else
        match (have, conv) with
        | Plan.Write_view, Some c -> Some (apply c e)
        | _ ->
          fail
            Pp.(
              str "a" ++ spc () ++ str (kind_name have) ++ spc () ++ strbrk "is passed to" ++ spc () ++ callee_name f
              ++ spc () ++ strbrk ("where a " ^ kind_name k ^ " is taken; a read view cannot be widened."))
    in
    match h with
    | View (have, g, tys) ->
      narrowed have
        (Option.map (fun text -> {custom = g; text; types = tys}) (Plan.find g).views.read_from_write)
    | Borrowed (c, tys) ->
      narrowed c.kind (Option.map (fun text -> {custom = c.mapped; text; types = tys}) c.read_from_write)
    | Canonical _ | Unknown -> None
  in
  (* The conversion of a canonical value [e] held as [h] to the view [t]
     takes.  Where the type [e] was declared at is not known (a structured
     binding), each type argument the conversion names is read back from
     [e]'s canonical type ({!read_back}). *)
  let from_canonical t (h : held) (e : expr) : conversion =
    match t with
    | Op_view (r, c, tys) -> {custom = r; text = c.from_canonical; types = tys}
    | Plan_view (k, g) -> (
      let text = (plan_view g k).from_canonical in
      match h with
      | Canonical (r, tys) when GlobRef.CanOrd.equal r g -> {custom = g; text; types = tys}
      | _ when not (names_type_arguments text) -> {custom = g; text; types = []}
      | _ -> {custom = g; text; types = read_back (Plan.find g) e} )
  in
  (* A copy of the canonical value, for a view that may not alias the
     caller's variable. *)
  let snapshot f t (e : expr) : expr =
    let k = target_kind t in
    let g = target_mapped t in
    let refuse () =
      fail
        Pp.(
          strbrk "a variable is passed to" ++ spc () ++ callee_name f ++ spc ()
          ++ strbrk ("both as a " ^ kind_name k ^ " of") ++ spc () ++ Printer.pr_global g ++ spc ()
          ++ strbrk
               "and where the callee may invalidate its views (InvalidatesViews, \
                a replacement): the view would dangle, and the type's view \
                cannot be copied (BorrowOnly), or a writable view would write \
                the copy.")
    in
    (* The copy is bound ahead of the statement, so that every place the
       callee's template puts its argument sees the same copy, which lives
       through the call. *)
    let copied conv text =
      match hoist (apply_once {conv with text} (apply conv e)) with
      | Some x -> apply conv x
      | None -> refuse ()
    in
    match (k, t) with
    | Plan.Read_view, Op_view (r, c, tys) -> (
      match c.materialise with
      | Some text -> copied {custom = r; text = c.from_canonical; types = tys} text
      | None -> refuse () )
    | Plan.Read_view, Plan_view _ -> (
      match (plan_view g k).escape with
      | Materialise text -> copied (from_canonical t (holding_of e) e) text
      | Borrow_only -> refuse () )
    | Plan.Write_view, _ -> refuse ()
  in
  let rec fe (e : expr) : expr =
    match e with
    | Call _ -> call ~escapes:true ~bound:false e
    | Local x -> (
      match holding x with
      | Borrowed _ as h -> materialised "view an operation returned" h e
      | _ -> e )
    | _ -> Cpp_ir.Map.expr (rw ()) e
  (* A call, its arguments converted; a borrowed view it returns is
     materialised where it [escapes]. *)
  and call ~escapes ~bound (e : expr) : expr =
    match e with
    | Call (sg, f, args) ->
      let n = List.length args in
      let target = targets u f n in
      let f = Cpp_ir.Map.expr (rw ()) f in
      let args =
        List.mapi
          (fun i (a : expr) ->
            match target i with
            | None -> fe a
            | Some t -> (
              (* A view takes nothing from its owner: a move there is
                 dropped. *)
              let a = match a with Move (Local _ as l) -> l | a -> a in
              match literal_view t a with
              | Some v -> v
              | None ->
              let h = holding_of a in
              let inner () = match a with Local _ -> a | Call _ -> call ~escapes:false ~bound a | _ -> fe a in
              match as_view f t h (inner ()) with
              | Some v -> v
              | None ->
                let aliased =
                  match a with
                  | Local x ->
                    List.exists Fun.id
                      (List.mapi
                         (fun j (b : expr) ->
                           j <> i
                           && (match b with Local y | Move (Local y) -> Id.equal x y | _ -> false)
                           && invalidating u f n j)
                         args)
                  | _ -> false
                in
                if aliased then snapshot f t a
                else
                  let conv = from_canonical t h a in
                  (* A view bound to a variable outlives the statement: a
                     temporary it is taken of is bound ahead of it. *)
                  let a = fe a in
                  if bound && not (free_to_repeat a) then
                    match hoist a with Some x -> apply conv x | None -> apply_once conv a
                  else apply_once conv a ))
          args
      in
      let e : expr = Call (sg, f, args) in
      ( match borrowed_call e with
      | Some (c, tys) when escapes -> materialised "view an operation returned" (Borrowed (c, tys)) e
      | _ -> e )
    | e -> fe e
  and stmts (ss : stmt list) : stmt list =
    List.concat_map
      (fun s ->
        let saved = !pending and saved_hoisting = !hoisting in
        pending := [];
        hoisting := true;
        let s = fs s in
        let ahead = List.rev !pending in
        pending := saved;
        hoisting := saved_hoisting;
        ahead @ [s])
      ss
  and fs (s : stmt) : stmt =
    match s with
    | While (c, body) ->
      let saved = !hoisting in
      hoisting := false;
      let c = fe c in
      hoisting := saved;
      While (c, stmts body)
    (* A borrowed view bound ahead of the call it is passed to stays a
       view; its uses decide whether it escapes. *)
    | Bind_variable (x, (Declare_deduced _ as b), init) when Option.has_some (borrowed_call init) ->
      Bind_variable (x, b, call ~escapes:false ~bound:true init)
    (* A view put in a variable of the canonical type -- a loop variable
       that holds its value ({!Control_to_cpp.Tail.held_across_turns}) set
       from a parameter the loop does not vary -- is the value copied out
       of it. *)
    | Bind_variable (x, (Declare (t, _) as b), (Local y | Move (Local y)))
      when Option.has_some (mapped_type t) && is_view (holding y) ->
      Bind_variable (x, b, materialised "view" (holding y) (Local y))
    | Bind_variable (x, Existing, (Local y | Move (Local y))) when is_canonical (holding x) && is_view (holding y) ->
      Bind_variable (x, Existing, materialised "view" (holding y) (Local y))
    | Expression (Binary (Assign, (Local x as l), (Local y | Move (Local y))))
      when is_canonical (holding x) && is_view (holding y) ->
      Expression (Binary (Assign, l, materialised "view" (holding y) (Local y)))
    | Foreign_block fb when Base.Table.is_mapped_operation fb.custom ->
      let f : expr = Entity (fb.custom, fb.type_args, Some {inline = Some (Cpp_ir.Foreign.template_of_text fb.template); custom_yields = None}) in
      ( match fe (Call (Cpp_ir.Build.signature ~nargs:(List.length fb.values) (), f, fb.values)) with
      | Call (_, _, values) -> Foreign_block {fb with values}
      | _ -> s )
    | _ -> Cpp_ir.Map.stmt (rw ()) s
  and rw () = Cpp_ir.Map.make ~stmts ~expr:fe ~stmt:fs ~type_:Fun.id () in
  stmts body

(* [e] with each string literal a call takes as a read view written as the
   view of the literal ({!literal_view}), in the body of a lambda it holds
   too. *)
let literal_views u (e : expr) : expr =
  let rec fe (e : expr) : expr =
    match e with
    | Call (sg, f, args) ->
      let target = targets u f (List.length args) in
      let args =
        List.mapi
          (fun i a ->
            match Option.bind (target i) (fun t -> literal_view t a) with Some v -> v | None -> fe a)
          args
      in
      Call (sg, fe f, args)
    | _ -> Cpp_ir.Map.expr (rw ()) e
  and fs (s : stmt) : stmt = Cpp_ir.Map.stmt (rw ()) s
  and rw () = Cpp_ir.Map.make ~expr:fe ~stmt:fs ~type_:Fun.id () in
  fe e

let transform_decl u (d : Cpp_ir.Lowered.Decl.t) : Cpp_ir.Lowered.Decl.t =
  let rec member ((f, a, b) : _ Cpp_ir.Field.member) : _ Cpp_ir.Field.member =
    match f with
    | Method m -> (Method {m with body = transform_body u m.params m.modes m.body}, a, b)
    | Nested_struct (x, ms) -> (Nested_struct (x, List.map member ms), a, b)
    | Out_of_line_declaration (Method m) ->
      (Out_of_line_declaration (Method {m with body = transform_body u m.params m.modes m.body}), a, b)
    | _ -> (f, a, b)
  in
  let rec decl (d : Cpp_ir.Lowered.Decl.t) : Cpp_ir.Lowered.Decl.t =
    match d with
    | Function ({shape = Definition (params, body); _} as fn) ->
      Function {fn with shape = Definition (params, transform_body u params fn.modes body)}
    | Template (ps, c, d) -> Template (ps, c, decl d)
    | Namespace (x, ds) -> Namespace (x, List.map decl ds)
    (* An initialiser converts implicitly where its callee takes a view;
       only a string literal, which would become a canonical string first,
       is made the view of itself. *)
    | Variable v -> Variable {v with init = literal_views u v.init}
    | Struct s -> Struct {s with fields = List.map member s.fields}
    | Merged_struct_members s -> Merged_struct_members {s with fields = List.map member s.fields}
    | Member_definition ({member = Method m; _} as md) ->
      Member_definition {md with member = Method {m with body = transform_body u m.params m.modes m.body}}
    | _ -> d
  in
  decl d
