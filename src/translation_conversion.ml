(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Converting a value between two instantiations of one inductive: the
    converting-constructor expression, the wrappers between a field's storage
    and API forms, and the namespace qualification the types written inside
    such a conversion need. *)

open Names
open Util

(** What a converting constructor throws for a field it cannot convert.

    A converting constructor is generated for every constructor of the
    inductive, but at a given call only the one the source holds runs.  When
    the two instantiations disagree on a field of some other constructor there
    is no conversion to write, and none is needed: the branch is dead. *)
let inactive_field_message =
  "unreachable: inactive constructor field at this instantiation"

(** Recursively wrap each inductive application in its namespace so that
    the type printer produces fully-qualified names.  The [~skip]
    predicate controls which references are left unwrapped:
    [qualify_inductives] wraps all inductives, while
    [qualify_inductives ~skip:(Core.Ref.User.Set.mem g set)] leaves members of
    [set] bare.  Used when the rendered type will appear in
    a context where inductives may not be in scope (e.g. [clone_as_value]
    template arguments in standalone free functions). *)
let rec qualify_inductives ?(skip = fun _ -> false) (t : Cpp_ir.Lowered.Type.t) : Cpp_ir.Lowered.Type.t =
  let go = qualify_inductives ~skip in
  match t with
  | Entity_application (g, ts, es) -> (
    let core : Cpp_ir.Lowered.Type.t = Entity_application (g, List.map go ts, es) in
    match g with
    | GlobRef.IndRef _ when skip g -> core
    | GlobRef.IndRef _ when Base.Table.is_inline_custom g -> core
    | GlobRef.IndRef _ -> In_namespace (g, core)
    | _ -> core )
  | In_namespace (g, t) -> (
    (* [go] may add the namespace to an application of [g] inside [t]; the
       wrapper is not doubled. *)
    let inner = go t in
    match inner with
    | In_namespace (g2, _) when GlobRef.CanOrd.equal g g2 -> inner
    | _ -> In_namespace (g, inner) )
  | Shared_pointer t -> Shared_pointer (go t)
  | Reference (k, t) -> Reference (k, go t)
  | Const t -> Const (go t)
  | Pointer t -> Pointer (go t)
  | Function (args, ret) -> Function (List.map go args, go ret)
  | Named (id, ts) -> Named (id, List.map go ts)
  | External (id, ts) -> External (id, List.map go ts)
  | Non_deduced t -> Non_deduced (go t)
  | Rebind (h, x) -> Rebind (go h, go x)
  | Member (base, id) -> Member (go base, id)
  | t -> t

(** Whether [ty] mentions a [std::shared_ptr] anywhere, however deeply. *)
let contains_shared_ptr : Cpp_ir.Lowered.Type.t -> bool =
  Cpp_ir.Types.exists (function Shared_pointer _ -> true | _ -> false)

(** [is_access_path e] -- [e] is a chain of variable reads, dereferences,
    field selections and nullary accessors, so naming it twice in one
    expression duplicates no work and no side effect. *)
let rec is_access_path : Cpp_ir.Lowered.Expr.t -> bool = function
  | Local _ | This | Literal Null_pointer -> true
  | Dereference e | Member (e, _) | Project (e, _, _) | Access (_, e, _) -> is_access_path e
  | Access_call (_, e, _, []) -> is_access_path e
  (* Reading a [crane::field] is a read of the path, as dereferencing is. *)
  | Call (_, Runtime Cpp_ir.Crane_rt.Unbox_field, [e]) -> is_access_path e
  | _ -> false

(** Generate an inline C++ expression that converts [expr] from [src_ty] to
    [dst_ty].  Used at every boundary between the storage representation
    (where recursive fields are [shared_ptr]-wrapped) and the API
    representation (where they are bare values).

    Conversion cases:
    - [shared_ptr<S> -> shared_ptr<T>]: null-check, dereference, make_shared
    - [shared_ptr<T> -> T]: dereference (converting ctor if inner ≠ dst)
    - [T -> shared_ptr<T>]: wrap in make_shared
    - [Core.Type.Global_app(g, ts1) -> Core.Type.Global_app(g, ts2)]: same container, different elements
    - Everything else (type variables, scalars): converting constructor

    @param skip    predicate for GlobRefs to skip during qualification
    @param src_ty  the source C++ type
    @param dst_ty  the destination C++ type
    @param expr    the C++ expression to convert
    @return a [cpp_expr] that produces a value of type [dst_ty] *)

let gen_type_conversion_expr ?(skip = fun _ -> false) ~(src_ty : Cpp_ir.Lowered.Type.t)
    ~(dst_ty : Cpp_ir.Lowered.Type.t) (expr : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
  (* Every type built here lands inside a template body (a converting
     constructor, a [make_shared<...>] argument), so it must be spelled exactly
     as the printer spells the same type in the surrounding generated code:
     each one is handed to the printer as a type node ([Convert], [Allocate],
     {!Cpp_passes.Erasure.converting_ctor}), never rendered here. *)
  (* Strip a single namespace wrapper when it matches the inner application.
     [convert_core_type_to_cpp_type] wraps external inductives as
     [In_namespace (g, Entity_application (g, ...))] for qualified rendering,
     but for pattern matching we want the bare application. *)
  let strip_ns : Cpp_ir.Lowered.Type.t -> Cpp_ir.Lowered.Type.t = function
    | In_namespace (g, (Entity_application (g2, _, _) as core)) when GlobRef.CanOrd.equal g g2 -> core
    | t -> t
  in
  (* Save the original dst_ty (with its namespace wrapper, if any) before
     stripping.  The stripped form is used for structural comparison; the
     original is used for rendering converting constructors, which the
     printer spells with namespace qualification and [typename] keywords. *)
  let orig_dst_ty = dst_ty in
  let src_ty = strip_ns src_ty and dst_ty = strip_ns dst_ty in
  (* Build an expression that names [expr] twice.  An access path can simply
     be repeated; anything else is bound once as the parameter of an
     immediately-applied lambda, so that its effects happen once.
     [lambda_ty] is that lambda's return type. *)
  let naming_expr ~lambda_ty ~body =
    if is_access_path expr then body expr
    else
      let x = Id.of_string "_named" in
      Cpp_ir.Build.call
        (Cpp_ir.Build.lambda
           [(Reference (Forwarding, Auto), Some x)]
           (Some lambda_ty)
           [Return (Some (body (Local x)))]
           ~capture:Runs_in_place )
        [expr]
  in
  let is_variable : Cpp_ir.Lowered.Type.t -> bool = function
    | Variable (Index (_, Some _) | Named _) | Apply (Variable (Index (_, Some _) | Named _), _) -> true
    | _ -> false
  in
  if src_ty = dst_ty then expr
  else
    (* Different types: dispatch on wrapper structure. *)
    match (src_ty, dst_ty) with
    | Shared_pointer src_inner, Shared_pointer dst_inner when strip_ns src_inner = strip_ns dst_inner ->
      (* shared_ptr<S> → shared_ptr<T> where the pointee types are identical
         (they differ only in a namespace rendering wrapper).  The pointer is
         already the right type, and the pointee is immutable, so forward the
         existing pointer (a refcount bump / move) instead of dereferencing and
         re-[make_shared]ing a fresh, independent copy of the whole node. *)
      expr
    | Shared_pointer _, Shared_pointer dst_inner ->
      (* shared_ptr<S> → shared_ptr<T>: null-check, then allocate the pointee
         read at [T].  Handing the pointee straight to [make_shared] would ask
         [T] to be constructible from [S], which is only one of the ways a
         value crosses instantiations -- a [std::pair] is read component by
         component instead -- so ask the helper for the pointee and allocate
         what it gives back. *)
      naming_expr ~lambda_ty:dst_ty ~body:(fun x ->
          Conditional
            ( x,
              Cpp_ir.Build.call (Allocate (Heap, dst_inner)) [Convert (dst_inner, Dereference x)],
              Literal Null_pointer ) )
    | Shared_pointer inner, _ ->
      (* shared_ptr<T> → T: dereference.  Also strip the namespace from inner
         before comparing to dst_ty: strip_ns was applied to dst_ty at the
         top of this function but not to inner (which sits one level deeper
         inside the pointer).  Without stripping inner, a namespaced list
         inner would wrongly appear different from the stripped dst_ty and
         generate a spurious converting constructor with an unqualified type
         name. *)
      let inner = strip_ns inner in
      let derefed : Cpp_ir.Lowered.Expr.t = Dereference expr in
      if inner = dst_ty then derefed else Cpp_passes.Erasure.converting_ctor orig_dst_ty [derefed]
    | _, Shared_pointer inner -> Cpp_ir.Build.call (Allocate (Heap, inner)) [expr]
    | Entity_application (g1, src_ts, _), Entity_application (g2, dst_ts, _)
      when GlobRef.CanOrd.equal g1 g2 && src_ts <> dst_ts && not (Base.Table.is_inline_custom g1) ->
      (* Same type at different arguments.  A converting constructor is the
         usual way across, but not every type has one -- [std::pair]'s asks
         each component to be constructible from the other's, and an erased
         component has to be cast rather than constructed -- so ask the helper,
         which uses the constructor where there is one and takes the value
         apart where there is not. *)
      Convert (orig_dst_ty, expr)
    (* A function at another result type: [crane_convert] reads what it
       returns. *)
    | Function (src_dom, _), Function (dst_dom, _) when List.length src_dom = List.length dst_dom ->
      Convert (orig_dst_ty, expr)
    | _ when is_variable src_ty && is_variable dst_ty ->
      (* Type-variable-to-type-variable conversion in converting constructors
         -- a family's field [E X] is one too, written [E] once the family is
         a plain parameter.
         A plain converting constructor [A(field)] is wrong here: at runtime
         [U] may be [std::any], and [pair<K,V>] has no constructor from one --
         nor from [pair<any,any>], which is how a pair's components are boxed
         one at a time.  Dispatch at compile time instead. *)
      if not (is_access_path expr) then Cpp_passes.Erasure.converting_ctor orig_dst_ty [expr]
      else
        (* Which way [U] is read at [A] -- unboxed, converted, or taken apart
           component by component -- cannot be decided until C++ substitutes
           [U], and [crane_convert] is exactly that decision, so ask it rather
           than restate a part of it here.  The one question left is whether
           there is any route at all: where there is none the field belongs to
           a constructor this instantiation never holds. *)
        let dst = qualify_inductives ~skip orig_dst_ty in
        Cpp_ir.Build.iife (Some dst)
          [ If_constexpr
              { test = Convertible (dst, Reference (Lvalue, Const src_ty));
                then_ = [Return (Some (Convert (dst, expr)))];
                (* [U] is neither a box nor anything else [A] can be read
                   from.  A converting constructor converts every field of
                   every constructor, but only the constructor the source
                   actually holds is reached; the rest are converted only
                   because C++ compiles both sides of an [if].  Two
                   instantiations that agree on the field being carried can
                   disagree completely on one that is not, so the unreachable
                   side gets the throw rather than a conversion no one asked
                   for. *)
                else_ = [Throw inactive_field_message] } ]
    (* A custom-mapped list at a known element type, under any namespace
       wrapper: only an erased source needs unboxing. *)
    | _, (Entity_application (g, [elem_ty], _) | In_namespace (_, Entity_application (g, [elem_ty], _)))
      when Base.Type_util.is_custom_list_global g && elem_ty <> Any && elem_ty <> Auto -> (
      match src_ty with
      | Any -> Cpp_passes.Erasure.unbox (Entity_application (g, [Any], [])) expr
      | _ -> expr )
    | _ ->
      (* Type variables or fully concrete different types: converting
         constructor.  Type variables are always bare (never shared_ptr)
         because nested self-references are wrapped at the field level. *)
      Cpp_passes.Erasure.converting_ctor orig_dst_ty [expr]

(** Wrap [expr] when [storage_ty] and [api_ty] differ due to pointer
    wrapping.  Converts from API form to storage form (e.g. bare value →
    [shared_ptr]).  No-op when the types match or neither involves smart
    pointers. *)
let wrap_storage_expr ~(storage_ty : Cpp_ir.Lowered.Type.t) ~api_ty expr =
  if storage_ty <> api_ty && contains_shared_ptr storage_ty then
    gen_type_conversion_expr ~src_ty:api_ty ~dst_ty:storage_ty expr
  else expr

(** Like {!wrap_storage_expr} but converts from storage form to API form
    (e.g. [shared_ptr] → bare value). *)
let wrap_api_expr ~(storage_ty : Cpp_ir.Lowered.Type.t) ~api_ty expr =
  if storage_ty <> api_ty && contains_shared_ptr storage_ty then
    gen_type_conversion_expr ~src_ty:storage_ty ~dst_ty:api_ty expr
  else expr

(** Strip a single [Tnamespace] wrapper off a namespaced [Core.Type.Global_app], leaving any
    other type untouched. Used to see through the namespace qualifier when
    classifying list-like globals. *)
let strip_ns_global_app : Cpp_ir.Lowered.Type.t -> Cpp_ir.Lowered.Type.t = function
  | In_namespace (_, (Entity_application _ as inner)) -> inner
  | t -> t

(** Strip self-referential [Tnamespace] wrappers, at every depth.

    Flat single-file extraction sometimes wraps a module-local inductive in
    [Tnamespace (g, Core.Type.Global_app (g, ...))], which renders as the bogus
    [typename G::G<...>].  Unwrapping those leaves a well-formed type; every
    other namespace qualifier is preserved. *)
let rec clean_self_ns (t : Cpp_ir.Lowered.Type.t) : Cpp_ir.Lowered.Type.t =
  match t with
  | In_namespace (ns_r, Entity_application (g_r, args, gns)) when GlobRef.CanOrd.equal ns_r g_r ->
    clean_self_ns (Entity_application (g_r, args, gns))
  | In_namespace (ns_r, inner) -> In_namespace (ns_r, clean_self_ns inner)
  | Entity_application (gr, args, ns) -> Entity_application (gr, List.map clean_self_ns args, ns)
  | Reference (k, t) -> Reference (k, clean_self_ns t)
  | Shared_pointer t -> Shared_pointer (clean_self_ns t)
  | t -> t
