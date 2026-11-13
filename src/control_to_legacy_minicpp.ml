(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Names
open Cpp_ir.Type
open Cpp_ir.Stmt
open Cpp_ir.Expr

type ty = Loopify_analysis.ty
type stmt = Loopify_analysis.stmt
type decl = Loopify_analysis.decl
type lambda = Loopify_analysis.lambda
type meth = Loopify_analysis.meth
type func = Loopify_analysis.func

(* How a loop is lowered: a tail loop, one built tail modulo cons, or a
   machine with a stack of frames. *)
type lowering =
  | Tail
  | Modulo_cons
  | Frames

(* How the recursion plan's [strategy] lowers a loop. *)
let lowering_of (strategy : Recursion_plan.strategy option) =
  match strategy with
  | Some Tail_loop -> Some Tail
  | Some (Modulo_cons _) -> Some Modulo_cons
  | Some Frame_stack -> Some Frames
  | Some (No_loop | Suspended _) | None -> None

(* The loop [target] of the definition [r], lowered as [planned], where
   that is one of the ways [lowerings]: a tail loop's turns build nothing
   and one tail modulo cons builds in some turn; a machine's ControlIR may
   be either, for a function whose chains its constructors' fields do not
   allow is a machine too, and a machine alone has entries. *)
let shaped_loop ~lowerings r planned target =
  match planned with
  | Some lowering when List.mem lowering lowerings -> (
    match Lower_control.loop target with
    | Some (Loop l) when Control_ir.Term.continues l.body <> [] && (Control_ir.Term.entries l.body = [] || lowering = Frames) ->
      let builds = Control_ir.Term.continues_into l.body <> [] in
      let shaped = match lowering with Tail -> not builds | Modulo_cons -> builds | Frames -> true in
      if shaped then Some (l, lowering)
      else begin
        Probe.violation "control IR"
          Pp.(
            str "the ControlIR of " ++ str (Table.kername_of_global r)
            ++ str (if builds then " builds what a tail loop does not" else " builds no constructor the plan's chains do") );
        None
      end
    | Some _ | None -> None )
  | Some _ | None -> None

(* The loop the recursion plan lowers the function [r] to, and how, where
   it lowers it in one of the ways [lowerings]. *)
let loop_of ~lowerings r =
  if Option.has_some (Lifted.of_ref r) then None
  else
    shaped_loop ~lowerings r
      (lowering_of (Recursion_plan.strategy ~pointer_fields:Loopify_analysis.constructor_pointer_fields r))
      (Control_ir.Loop.Function r)

(* The loop of the function [r], and how it is lowered, where it is one
   this module lowers. *)
let planned_loop r = if Table.should_loopify r then loop_of ~lowerings:[Tail; Modulo_cons; Frames] r else None

(* The loop of the method made of [r], and how it is lowered, where it is
   one this module lowers. *)
let method_loop r = loop_of ~lowerings:[Tail; Modulo_cons; Frames] r

(* Why a loop the plan commits to was left as it was generated. *)
let reason = function
  | Loopify.Declined why | Left (Some why) -> why
  | Left None -> "left as generated"

let in_place = Recursion_plan.in_place

(* What each parameter of the loop [l] is passed by its Continues
   ({!Control_ir.Term.parts_passed}), read with the planned representation. *)
let parts_passed l =
  Control_ir.Term.parts_passed ~pointer_fields:Loopify_analysis.constructor_pointer_fields ~in_place l

(* Whether every Continue of the loop [l] passes each of its parameters a
   value derived from one of them ({!Control_ir.Term.derived_passed}). *)
let derived_passed l =
  Control_ir.Term.derived_passed ~pointer_fields:Loopify_analysis.constructor_pointer_fields ~in_place l

(* The points a machine with a stack of frames, lowered from a body of the
   definition [origin] standing under [depth] of its binders, resumes at.
   A frame keeps the binders bound before a point that what follows reads,
   except those [available] -- the parameters of its loop every turn passes
   on unchanged, which the machine holds outside its frames -- and holds
   itself those of them its handler does not bind again: one recomputable
   from what is available, or bound again so, in turn, as the machine does
   ({!Loopify_frame}'s [rebuilt_binders]).  Of those, what follows passes on
   to a call entering the machine those it may keep as pointers: Loopify
   keeps one so where the entry takes the parameter by pointer, which
   {!Frame_storage} decides from the C++ parameters, after the plan. *)
let resumes_of ?entry_captures ~origin ~depth ~available ~parameters:(first, (l : Control_ir.Term.loop)) () :
    Ownership_ir.resumes =
  let rebuilt (p : Recursion_plan.resume) =
    List.fold_left
      (fun rebuilt (c : Recursion_plan.recomputable) ->
        if List.for_all (fun b -> available b || List.exists (Core_binder.equal b) rebuilt) c.from then
          c.recomputed :: rebuilt
        else rebuilt )
      [] p.recomputable
  in
  { origin;
    depth;
    entry_captures;
    parameter_type = (fun level -> if level < first then None else Option.map snd (List.nth_opt l.parameters (level - first)));
    resume_at =
      (fun b ->
        match Recursion_plan.resumes_binding b with
        | [p] ->
          let kept = List.filter (fun b -> not (available b)) p.live in
          let rebuilt = rebuilt p in
          let held = List.filter (fun b -> not (List.exists (Core_binder.equal b) rebuilt)) kept in
          Some
            { calls = List.map (fun (c : Recursion_plan.call) -> c.occurrence) p.after;
              kept;
              held;
              passed =
                List.filter
                  (fun b -> List.exists (fun (q : Recursion_plan.passing) -> Core_binder.equal q.passed b) p.passes)
                  held }
        | _ -> None ) }

(* Whether the Core binder [b] is a parameter of the loop [l], whose first
   parameter is at the level [first], that every turn passes on unchanged. *)
let invariant_at (l : Control_ir.Term.loop) ~first =
  let invariant = Control_ir.Term.invariant_parameters l in
  fun (b : Core_binder.t) -> b.level >= first && Option.default false (List.nth_opt invariant (b.level - first))

(* The loop of the function [r] where its body is lowered as a machine with
   a stack of frames as it is generated ({!lower_group}): one the
   configuration loopifies and the recursion plan lowers so, adopting at
   most one local fixpoint, as its ControlIR's entry, so that nothing
   decided after the plan leaves its calls as generated. *)
let function_machine r =
  let frames =
    Table.should_loopify r
    && Option.is_empty (Lifted.of_ref r)
    && Recursion_plan.strategy ~pointer_fields:Loopify_analysis.constructor_pointer_fields r
       = Some Recursion_plan.Frame_stack
  in
  match if frames then Lower_control.loop (Control_ir.Loop.Function r) else None with
  | Some (Control_ir.Term.Loop l) when List.compare_length_with (Control_ir.Term.entries l.body) 1 <= 0 -> Some l
  | Some _ | None -> None

let function_resumes r ~depth =
  Option.map
    (fun l -> resumes_of ~origin:r ~depth ~available:(invariant_at l ~first:0) ~parameters:(0, l) ())
    (function_machine r)

let method_resumes r ~inductive ~receiver ~depth =
  (* Its struct's methods are loopified where everything is, if the struct
     is merged into its module's, and as its inductive says otherwise
     ({!lower_methods}): which, the method is generated before it is told. *)
  let either = Table.loopify () || Table.loopifies_methods_of inductive in
  let both = Table.loopify () && Table.loopifies_methods_of inductive in
  match method_loop r with
  | Some (l, Frames)
    when Table.loopifies_method r && either && Control_ir.Term.entries l.body = []
         && Option.default false (List.nth_opt (derived_passed l) receiver) ->
    Some (resumes_of ~origin:r ~depth ~available:(invariant_at l ~first:0) ~parameters:(0, l) (), both)
  | Some _ | None -> None

(* A loop as it is lowered, and for each C++ parameter of what it is
   lowered from, whether the loop varies it -- some Continue changes the
   parameter of the loop it stands for -- and whether every Continue passes
   it a value stored in what the caller passed for it
   ({!Control_ir.Term.parts_passed}).  A parameter standing for none of the
   loop's is neither.  A loop built tail modulo cons may recycle the cells
   of an input it walks into its own ({!Reuse_cursor}).  A tail loop moves
   a parameter into its own next value at a Continue where the plan says
   so ({!Ownership_ir.continue_moves}). *)
type planned = {
  loop : Control_ir.Term.loop;
  lowering : lowering;
  varying : bool list;
  parts : bool list;
  cursor : Reuse_cursor.t option;
  moves : (Miniml.Occurrence.t * Ownership_ir.Continue_move.t list) list;
}

(* [l] lowered as [lowering] from what takes C++ parameters standing, in
   order, for the parameters of [l] at [positions], or for none of them. *)
let planned_at (l : Control_ir.Term.loop) lowering positions =
  let at flags = List.map (function Some i -> List.nth flags i | None -> false) positions in
  { loop = l;
    lowering;
    varying = at (List.map not (Control_ir.Term.invariant_parameters l));
    parts = at (parts_passed l);
    cursor =
      ( match lowering with
      | Modulo_cons ->
        Option.bind
          (Reuse_cursor.plan ~pointer_fields:Loopify_analysis.constructor_pointer_fields ~in_place l)
          (fun c -> Reuse_cursor.positioned c positions)
      | Tail | Frames -> None );
    moves =
      ( match lowering with
      | Tail ->
        List.map
          (fun (o, moves) -> (o, List.map (function Some i -> List.nth moves i | None -> Ownership_ir.Continue_move.Keep) positions))
          (Ownership_ir.continue_moves l)
      | Modulo_cons | Frames -> [] ) }

(* The position among the parameters of the loop [l] of the parameter of
   the function [r] the Core binder [b] is, where it is one. *)
let position r (l : Control_ir.Term.loop) (b : Core_binder.t option) =
  match b with
  | Some b when GlobRef.UserOrd.equal b.origin r && b.level < List.length l.parameters -> Some b.level
  | Some _ | None -> None

let binder_of binders (id, _) = List.find_map (fun (x, b) -> if Id.equal x id then Some b else None) binders

(* The loop the function [f] is lowered to, where it is one this module
   lowers, each of its C++ parameters standing for one of the loop's. *)
let planned (f : func) =
  match (f.shape, f.path.inner) with
  | Definition (params, _), [] ->
    let r = fst f.path.outer in
    Option.bind (planned_loop r) (fun (l, lowering) ->
        let positions = List.map (fun p -> position r l (binder_of f.binders p)) params in
        if List.for_all Option.has_some positions then Some (planned_at l lowering positions) else None )
  | (Definition _ | Declaration _), _ -> None

(* The jump a C++ call is, where it is made of one of the Continues
   [continues]: the arguments it passes the loop's parameters. *)
let jump continues : Loopify_analysis.call_checker = function
  | Call ({occurrence = Some o; _}, _, args) when List.exists (Miniml.Occurrence.equal o) continues ->
    Some (Loopify_analysis.mk_call_site (List.rev args))
  | _ -> None

(* Under [CRANE_CHECK_IR]: the [loop] the function [f] is lowered to takes
   the calls [jumped], which must be its Continues [continues]. *)
let check_jumps ~loop (f : func) ~continues ~jumped =
  if not (Loopify_analysis.made_as_planned continues jumped) then
    Probe.violation "control IR"
      Pp.(
        str "the calls the " ++ str loop ++ str " of "
        ++ str (Table.kername_of_global (fst f.path.outer))
        ++ str " takes are not its Continues" )

(* Whether a frame can hold a parameter declared at [ty] by pointer: one
   borrowed of a value type ({!Loopify_tail.borrowed_value_param_pointee}). *)
let holdable_type ty = Option.has_some (Loopify_tail.borrowed_value_param_pointee ty)

(* Whether a frame can hold by pointer the parameter at declared position
   [k] of the callable [r], of Core type [ty], as [r]'s callable plan passes
   it ({!Frame_storage.passed_holdable}).  [None] where no plan states how
   [r] passes its parameters. *)
let planned_holdable r k ty =
  Option.map
    (fun passing -> Frame_storage.passed_holdable (List.nth_opt passing k) ty)
    (Option.bind (Callable_abi.lookup r) Callable_abi.passing)

(* [held k cty] for {!storage_at} of the machine of the callable [r], its
   loop [l], the C++ parameter at [k] declared at [cty] and standing for the
   loop's parameter [positions] gives: as [r]'s plan passes the parameter at
   declared position [declared k] ({!planned_holdable}); where no plan says,
   or it stands for none of [l]'s, as its declared type does
   ({!holdable_type}).  The two differ only under Reuse with NonAtomicRc,
   where the declared type takes any value it does not recognise as boxed
   -- an enum, or an alias of an erased type -- for a value inductive.  A
   frame spells the pointer from the declared type: one the plan holds by
   pointer that it cannot spell so is held by value, and reported under
   [CRANE_CHECK_IR]. *)
let planned_held r (l : Control_ir.Term.loop) positions ~declared k cty =
  match List.nth_opt positions k with
  | Some (Some i) -> (
    match planned_holdable r (declared k) (snd (List.nth l.parameters i)) with
    | Some true when not (holdable_type cty) ->
      Probe.violation "frame storage"
        Pp.(
          str "the plan of " ++ str (Table.kername_of_global r) ++ str " lends its parameter " ++ int (declared k)
          ++ str " for a frame to hold by pointer, at a declared type no pointer spells" );
      false
    | Some planned -> planned
    | None -> holdable_type cty )
  | Some None | None -> holdable_type cty

(* The parameters of every local fixpoint's lambda in [stmts], each by the
   Core binder translation records it binds, with the type it declares. *)
let fixpoint_parameters stmts =
  let found = ref [] in
  let rec fe e =
    ( match e with
    | Lambda {fixpoint = Some _; params; binders; _} ->
      List.iter
        (fun (ty, x) ->
          match Option.bind x (fun x -> List.assoc_opt x binders) with
          | Some b -> found := (b, ty) :: !found
          | None -> () )
        (List.rev params)
    | _ -> () );
    Loopify_analysis.map_expr fe fs Fun.id e
  and fs s = Loopify_analysis.map_stmt fe fs Fun.id s in
  List.iter (fun s -> ignore (fs s)) stmts;
  !found

(* The positions among the parameters of the loop [l] of those the C++
   parameters [params] of a helper lifted out for the function of a local
   fixpoint stand for, as a definition stores them, the last first
   ({!Cpp_ir.Function.shape}): the variables the helper captures, stored
   first, stand for none, every call passing them on as they are; the rest
   for the parameters of [l] that are not void
   ({!Ml_type_util.void_binder}), the last first.  [None] where they are
   not so many. *)
let lifted_positions (l : Control_ir.Term.loop) params =
  let kept =
    List.filter_map
      (fun (i, (_, ty)) -> if Ml_type_util.void_binder ty then None else Some i)
      (List.mapi (fun i p -> (i, p)) l.parameters)
  in
  let captured = List.length params - List.length kept in
  if captured < 0 then None else Some (List.init captured (fun _ -> None) @ List.rev_map (fun i -> Some i) kept)

(* How the frames of a machine, its loop [l], hold its parameters and those
   of the loops its entries enter ({!Frame_storage}), as each is
   represented: a parameter of the loop by the C++ parameter of [params]
   standing for it, at its position in [positions] ([None]: it stands for
   none, and no frame holds it by pointer), held by pointer where [held k ty]
   of the one at [k] of type [ty]; one of an entered loop, where the machine
   is the function [entering]'s, as the plan of the local fixpoint the loop
   is made from passes it ({!Frame_storage.local_holdable}) -- with no
   [entering], none is held by pointer.  Under [CRANE_CHECK_IR], the
   parameter of the fixpoint's lambda in [body] binding it, the Core binder
   counting from [entering]'s parameters, must be declared at a type a
   pointer spells exactly where the plan holds it so.  The parameters'
   flags, in order, and those of the entered loops' by the Core binder. *)
let storage_at ?entering (l : Control_ir.Term.loop) positions params ~held body =
  let lambda_params = lazy (if Option.has_some entering then fixpoint_parameters body else []) in
  let of_entering (b : Core_binder.t) = Option.cata (fun r -> GlobRef.UserOrd.equal b.origin r) false entering in
  let holdable : Frame_storage.parameter -> bool = function
    | Own i -> List.exists2 (fun p (k, (_, ty)) -> p = Some i && held k ty) positions (List.mapi (fun k p -> (k, p)) params)
    | Entered {loop; index; level} ->
      let planned = Option.has_some entering && Frame_storage.local_holdable loop index = Some true in
      Frame_storage.check_local index ~planned ~declared:(fun () ->
          List.exists
            (fun ((b : Core_binder.t), ty) -> of_entering b && b.level = level && holdable_type ty)
            (Lazy.force lambda_params) );
      planned
  in
  let storage = Frame_storage.plan ~pointer_fields:Loopify_analysis.constructor_pointer_fields ~in_place ~holdable l in
  let own_pointers =
    List.map (function Some i -> List.nth storage.own i = Ownership_ir.Storage.Local | None -> false) positions
  in
  let entered (b : Core_binder.t) =
    of_entering b && List.assoc_opt b.level storage.entered = Some Ownership_ir.Storage.Local
  in
  (own_pointers, entered)

(* The same, of the machine of the function [f], its C++ parameters
   [params]: of a function's loop where every parameter stands for one of
   the loop's; of the loop of the local fixpoint a helper is lifted for by
   the helper's positions ({!lifted_positions}), the variables it captures
   standing for none and no parameter of an entered loop held by pointer, as
   a local machine's ({!Loopify.member_plan}).  [None] otherwise. *)
let machine_storage (f : func) params body (l : Control_ir.Term.loop) =
  match l.loop with
  | Member _ ->
    let r = fst f.path.outer in
    if Option.has_some (Lifted.of_ref r) then
      Option.map
        (fun positions ->
          let n = List.length params in
          storage_at l positions params ~held:(planned_held r l positions ~declared:(fun k -> n - 1 - k)) body )
        (lifted_positions l params)
    else None
  | Function r ->
    let positions = List.map (fun p -> position r l (binder_of f.binders p)) params in
    if not (List.for_all Option.has_some positions) then None
    else
      let n = List.length params in
      Some (storage_at ~entering:r l positions params ~held:(planned_held r l positions ~declared:(fun k -> n - 1 - k)) body)

(* The function [f], generated under the template parameters [tparams],
   lowered to the loop [l] varying the parameters [varying]; [Error why]
   where Loopify makes no loop of it -- a call passing the loop other
   arguments than it has parameters, say -- for the reason [why]
   ({!Loopify.unlowered}). *)
let rec lower_function ~tparams (f : func) {loop = l; lowering; varying; parts; cursor; moves} =
  match (f.shape, lowering) with
  | Declaration _, _ -> Error (Loopify.Left None)
  | Definition (params, body), Modulo_cons ->
    lower_modulo_cons ~tparams f params body l ?cursor ~varying ~parts (Control_ir.Term.continues_into l.body)
  | Definition (params, body), Frames -> lower_frames ~tparams f params body l ~varying ~parts
  | Definition (params, body), Tail -> (
    let continues = Control_ir.Term.continues l.body in
    let jumps = ref [] in
    let jumped e = jumps := Loopify_analysis.made_of e :: !jumps in
    let exposed = Loopify_analysis.expose_tail_calls (jump continues) body in
    match Loopify_tail.transform_tail ~jumped ~moves ~varying ~parts tparams (jump continues) params f.return_type exposed with
    | exception Loopify_analysis.Not_linearisable why -> Error (Loopify.Declined why)
    | loop -> (
      if Probe.checking () then check_jumps ~loop:"tail loop" f ~continues ~jumped:(List.rev !jumps);
      match Loopify.after_tail_loop ~tparams f params loop with
      | exception Loopify_analysis.Not_linearisable why -> Error (Loopify.Declined why)
      | body -> Ok {f with shape = Definition (params, body); loop = Some l.loop} ) )

(* The function [f] lowered to the loop [l] tail modulo cons, building the
   cells of its turns [into] around the calls they continue by. *)
and lower_modulo_cons ~tparams (f : func) params body l ?cursor ~varying ~parts into =
  let continues = Control_ir.Term.continues l.body in
  let shapes = Loopify_tmc.control_shapes into in
  let jumps = ref [] in
  let jumped e = jumps := Loopify_analysis.made_of e :: !jumps in
  let exposed = Loopify_analysis.expose_tail_calls (jump continues) body in
  match Loopify.modulo_cons_loop ~jumped ?cursor ~varying ~parts ~shapes ~tparams (jump continues) f params exposed with
  | exception Loopify_analysis.Not_linearisable why -> Error (Loopify.Declined why)
  | None -> Error (Loopify.Left None)
  | Some loop -> (
    if Probe.checking () then check_jumps ~loop:"loop tail modulo cons" f ~continues ~jumped:(List.rev !jumps);
    match Loopify.after_tail_loop ~strategy:Lp_tmc ~tparams f params loop with
    | exception Loopify_analysis.Not_linearisable why -> Error (Loopify.Declined why)
    | body -> Ok {f with shape = Definition (params, body); loop = Some l.loop} )

(* The function [f] lowered to the machine with a stack of frames of its
   loop [l], entered by the calls made of [l]'s Continues of it, and by
   those of the entry it adopts, if it has one: the body Loopify finds of
   it ({!Loopify.frame_machine}). *)
and lower_frames ~tparams (f : func) params body (l : Control_ir.Term.loop) ~varying ~parts =
  let own = Control_ir.Term.continues_of l.loop l.body in
  let exposed = Loopify_analysis.expose_tail_calls (jump own) body in
  let parts, entered_pointers =
    match machine_storage f params body l with
    | Some (own_pointers, entered_pointers) -> (List.map2 ( || ) parts own_pointers, Some entered_pointers)
    | None -> (parts, None)
  in
  let machine () =
    match Control_ir.Term.entries l.body with
    | [] -> Loopify.frame_machine ~loop:l.loop ~varying ~parts ~tparams (jump own) f params exposed
    | [entry] ->
      Loopify.frame_machine ~loop:l.loop ~entry:entry.loop ?entered_pointers ~varying ~parts ~tparams (jump own) f
        params exposed
    | _ :: _ :: _ -> Error (Loopify.Left None)
  in
  match machine () with
  | exception Loopify_analysis.Not_linearisable why -> Error (Loopify.Declined why)
  | Error why -> Error why
  | Ok (machine, survived) -> (
    match Loopify.after_tail_loop ~strategy:Lp_frame ?survived ~tparams f params machine with
    | exception Loopify_analysis.Not_linearisable why -> Error (Loopify.Declined why)
    | body -> Ok {f with shape = Definition (params, body); loop = Some l.loop} )

(* The function a generated declaration is, with the template parameters
   it is generated under. *)
let rec function_of ?(tparams = []) : decl -> _ = function
  | Template (tparams, _, d) -> function_of ~tparams d
  | Function f -> Some (tparams, f)
  | _ -> None

let rec with_function f : decl -> decl = function
  | Template (tparams, c, d) -> Template (tparams, c, with_function f d)
  | Function _ -> Function f
  | d -> d

(* Whether Loopify loopifies the definition [r]: a method as its struct's
   methods are loopified. *)
let loopified r =
  match Cpp_state.is_registered_method r with
  | Some (inductive, _) -> Table.loopifies_methods_of inductive && Table.loopifies_method r
  | None -> Table.should_loopify r

(* Whether Loopify makes a machine with a stack of its own of the definition
   [r] and lowers the local fixpoints in its body only around that
   machine. *)
let machine r =
  loopified r
  &&
  match Recursion_plan.strategy ~pointer_fields:Loopify_analysis.constructor_pointer_fields r with
  | Some (Modulo_cons _ | Frame_stack) -> true
  | Some (No_loop | Tail_loop | Suspended _) | None -> false

(* Whether Loopify lowers every local fixpoint in the body of the
   definition [r], machines included, [function_] saying whether that body
   is a function's: a function it loopifies, with its loop
   ({!Loopify.after_tail_loop}) or, where none is made, alone
   ({!lower_locals}), not a helper lifted out of another definition.  Of any other body it lowers the local tail
   loops alone. *)
let lowers_local_machines ~function_ r = function_ && Table.should_loopify r && not (Option.has_some (Lifted.of_ref r))

(* How {!local_loop} lowers the local fixpoint [member], if at all.  The
   function a fixpoint is in the flow of adopts it only where it is a
   machine itself, which a local tail loop is never lowered inside. *)
let local_lowering ~owner ~function_ ~lifted ~member:((occurrence, _) as member) =
  match Recursion_plan.strategy_at ~pointer_fields:Loopify_analysis.constructor_pointer_fields member with
  | Some Tail_loop ->
    if Recursion_plan.adoptable_by_fixpoint ~lifted occurrence || Option.cata machine false owner then None
    else Some Tail
  | Some (Modulo_cons _ | Frame_stack)
    when (not (Recursion_plan.adoptable_somewhere ~lifted occurrence))
         && Option.cata (lowers_local_machines ~function_) false owner ->
    Some Frames
  | Some (No_loop | Modulo_cons _ | Frame_stack | Suspended _) | None -> None

let local_resumes ~owner ~function_ ~lifted ~member ~depth ~arity =
  (* The machine of the function [owner] adopting the fixpoint as its
     entry re-enters it with every parameter it takes, its captures among
     them: a frame of the entry's keeps whatever what follows reads. *)
  let adopted =
    match Option.bind owner function_machine with
    | Some l ->
      List.find_opt
        (fun (e : Control_ir.Term.loop) -> Control_ir.Loop.equal e.loop (Member (fst member, snd member)))
        (Control_ir.Term.entries l.body)
    | None -> None
  in
  (* A machine of its own: one {!local_loop} makes, or, of a fixpoint the
     plan lowers so that it does not take, perhaps one Loopify makes of the
     Y-combinator it is then generated as, in a body it loopifies. *)
  let own =
    match local_lowering ~owner ~function_ ~lifted ~member with
    | Some Frames -> Some true
    | Some (Tail | Modulo_cons) -> None
    | None -> (
      match Recursion_plan.strategy_at ~pointer_fields:Loopify_analysis.constructor_pointer_fields member with
      | Some (Modulo_cons _ | Frame_stack) -> Some false
      | Some (No_loop | Tail_loop | Suspended _) | None -> None )
  in
  match (owner, adopted, own) with
  | Some origin, Some entered, _ ->
    Some
      ( resumes_of ~entry_captures:(arity + 1) ~origin ~depth ~available:(fun _ -> false)
          ~parameters:(depth - arity, entered) (),
        true )
  | Some origin, None, Some certain -> (
    match Lower_control.loop (Control_ir.Loop.Member (fst member, snd member)) with
    | Some (Loop l) when Control_ir.Term.continues l.body <> [] ->
      (* What the body reads from outside the fixpoint is bound before the
         loop and in scope for all of it, as an invariant parameter is. *)
      let first = depth - arity in
      let invariant = invariant_at l ~first in
      Some (resumes_of ~origin ~depth ~available:(fun b -> b.level < first || invariant b) ~parameters:(first, l) (), certain)
    | Some _ | None -> None )
  | _ -> None

let lower_local_loop ~owner ~function_ ~lifted ~member ~tparams ~name (lam : lambda) : stmt option =
  let lowering = local_lowering ~owner ~function_ ~lifted ~member in
  let member_loop = Control_ir.Loop.Member (fst member, snd member) in
  let unlowered why =
    Loop_verdicts.record member_loop (Unlowered why);
    None
  in
  (* A loop or machine leaving a call behind is a decline, as Loopify
     records it of the Y-combinator then left. *)
  let declined () =
    Loopify_analysis.record_outcome (Id.to_string name) (Lp_declined Loopify_analysis.survived_generically);
    unlowered Loopify_analysis.survived_generically
  in
  match (Lower_control.loop member_loop, lowering) with
  | Some (Loop l), Some lowering when Control_ir.Term.continues l.body <> [] -> (
    let params = List.filter_map (fun (ty, x) -> Option.map (fun x -> (x, ty)) x) (List.rev lam.params) in
    match Loopify.member_plan ~frames:(lowering = Frames) member params with
    | None -> unlowered "its lambda takes other parameters than its loop"
    | Some {member_varying = varying; member_parts = parts; member_moves = moves} ->
      let continues = Control_ir.Term.continues l.body in
      let jumps = ref [] in
      let jumped e = jumps := Loopify_analysis.made_of e :: !jumps in
      let exposed = Loopify_analysis.expose_tail_calls (jump continues) lam.body in
      let ret_ty = Option.default Void lam.return_type in
      let body () =
        match lowering with
        | Tail | Modulo_cons ->
          Some (Loopify_tail.transform_tail ~jumped ~moves ~varying ~parts tparams (jump continues) params ret_ty exposed)
        | Frames ->
          Loopify.local_frame_machine ~member ~name ~binders:(Loopify_analysis.lambda_binders lam) ~varying ~parts ~tparams (jump continues) params ret_ty exposed
      in
      match body () with
      | exception Loopify_analysis.Not_linearisable why -> unlowered why
      | None -> declined ()
      | Some body ->
        (* A call of the fixpoint the loop does not take -- one in a closure
           it builds -- or the fixpoint named as a value calls a lambda that
           is no longer there: it stays the Y-combinator Loopify declines. *)
        let left = Loopify_analysis.calls_checker (Recursion_plan.member_calls member) in
        if Recursion_plan.named_as_value member || Loopify_analysis.body_exists (fun e -> Option.has_some (left e)) body
        then declined ()
        else begin
          if Probe.checking () && lowering = Tail
             && not (Loopify_analysis.made_as_planned continues (List.rev !jumps))
          then
            Probe.violation "control IR"
              Pp.(str "the calls the tail loop of the local fixpoint " ++ Id.print name ++ str " jumps at are not its Continues");
          if lowering = Tail then Loopify_analysis.record_outcome (Id.to_string name) Lp_tail;
          let loop = {lam with body = body; moved = []} in
          let moved = List.filter (fun x -> List.mem x (Loopify_analysis.free_vars_expr (Lambda loop))) lam.moved in
          Loop_verdicts.record member_loop Lowered;
          Some (Bind_variable (name, Declare (Auto, None), Lambda {loop with moved = moved}))
        end )
  (* A loop no call continues is none: every call is where no loop takes
     it, and declines it, where Loopify reaches the fixpoint -- in a body it
     loopifies. *)
  | Some _, Some _ when Option.cata loopified false owner ->
    Loopify_analysis.record_outcome (Id.to_string name) (Lp_declined Loopify_analysis.survived_generically);
    Loop_verdicts.record member_loop Kept;
    None
  | (Some _ | None), _ ->
    Loop_verdicts.record member_loop Kept;
    None

(* The positions among the parameters of the loop [l] of those the
   receiver and the parameters of the method [m], made of the function
   [r], stand for, as {!planned} reads a function's: [None] where one
   stands for none of [l]'s. *)
let method_positions r (l : Control_ir.Term.loop) (m : meth) =
  let positions =
    position r l m.receiver_binder :: List.map (fun p -> position r l (binder_of m.binders p)) m.params
  in
  if List.for_all Option.has_some positions then Some positions else None

(* The method [m] lowered to its loop, where it is one: the struct it is a
   member of declared under [tparams], its receiver a [self_ty].  It is
   Loopify's method transform: a tail loop varying the receiver and the
   parameters its ControlIR varies, a loop tail modulo cons or a machine
   taking the calls its ControlIR continues by
   ({!Loopify.transform_method_own}), pointing where every call passes a
   value stored in what the caller passed ({!parts_passed}) wherever its
   receiver and parameters each stand for a parameter of the loop.  A
   method the transform leaves as it was is declined -- a receiver a frame
   cannot point at -- and left to Loopify, which declines it. *)
let lower_method ~tparams ~self_ty (m : meth) =
  match Option.bind m.globref (fun r -> Option.map (fun planned -> (r, planned)) (method_loop r)) with
  | None ->
    Loopify.record_unlowered_method m;
    None
  | Some (r, (l, lowering)) -> (
    let unlowered why =
      Loop_verdicts.record l.loop (Unlowered why);
      None
    in
    let positions = method_positions r l m in
    let planned = Option.map (planned_at l lowering) positions in
    (* A frame or a cell keeps a pointer to the receiver across turns, which
       one made in a turn -- a call's result, a binder of a match on one --
       does not outlive.  A tail loop parks such a receiver, before the
       turn's other arguments are evaluated: where one of them reads the
       receiver it is not lowered either. *)
    let rebuilt =
      match (lowering, positions) with
      | Tail, Some (Some i :: _) ->
        Control_ir.Term.rebuilt ~pointer_fields:Loopify_analysis.constructor_pointer_fields ~in_place l i
      | (Modulo_cons | Frames | Tail), _ -> []
    in
    let value_receiver =
      match (lowering, positions) with
      | (Modulo_cons | Frames), Some (Some i :: _) when not (List.nth (derived_passed l) i) -> Some Loopify.value_receiver
      | Tail, _ when List.exists (fun (r : Control_ir.Term.rebuilt) -> r.read_elsewhere) rebuilt ->
        Some Loopify.rebuilt_receiver_read
      | (Modulo_cons | Frames | Tail), _ -> None
    in
    let park = List.map (fun (r : Control_ir.Term.rebuilt) -> r.turn) rebuilt in
    (* A machine holds a parameter by pointer where it lies in what the
       caller passed ({!Frame_storage}), the receiver -- [_self], a pointer
       to the caller's object -- among what it passed. *)
    let pointed parts =
      match (lowering, positions) with
      | Frames, Some positions ->
        let params = (Id.of_string "_self", self_ty) :: m.params in
        let held k ty = k = 0 || planned_held r l positions ~declared:(fun k -> k - 1) k ty in
        let own, _ = storage_at ~entering:r l positions params ~held m.body in
        List.mapi (fun k (part, pointer) -> part || (k > 0 && pointer)) (List.combine parts own)
      | (Frames | Modulo_cons | Tail), _ -> parts
    in
    let transform =
      match (lowering, planned) with
      | _ when Option.has_some value_receiver -> None
      | _, Some {varying; parts; cursor; moves; _} ->
        let parts = pointed parts in
        Some (fun () -> Loopify.transform_method_own ?cursor ~moves ~varying ~parts ~park ~tparams ~self_ty m)
      | _, None -> None
    in
    match (transform, value_receiver) with
    | None, Some why ->
      Loopify_analysis.record_outcome (Id.to_string m.name) (Lp_declined why);
      Loop_verdicts.record l.loop (Declined why);
      None
    | None, None ->
      Loopify.record_unlowered_method m;
      unlowered "its receiver and parameters stand for none of its loop's"
    | Some transform, _ -> (
      match transform () with
      | exception Loopify_analysis.Not_linearisable why -> unlowered why
      | Method m' when compare m' m <> 0 ->
        Loop_verdicts.record l.loop Lowered;
        Some
          { m' with
            body = Loopify.lower_local_tail_loops ~tparams:(tparams @ m.type_params) m'.body;
            loop = Some l.loop }
      | _ -> unlowered "Loopify's method transform left it" ) )

let lower_struct_methods ~merged inductive vars fields =
  let tparams = List.map (fun v -> ((Typename, v) : Loopify_analysis.param_kind * Id.t)) vars in
  let self_ty : ty = Const (Pointer (Entity_application (inductive, List.map Loopify_analysis.named_tvar vars, []))) in
  let loopified r =
    (if merged then Table.loopify () else Table.loopifies_methods_of inductive) && Table.loopifies_method r
  in
  List.map
    (fun (((f, vis, tag) as field) : Loopify_analysis.phase Cpp_ir.Field.member) ->
      match f with
      | Method ({globref = Some r; _} as m) ->
        if loopified r then
          match lower_method ~tparams ~self_ty m with Some m -> (Cpp_ir.Field.Method m, vis, tag) | None -> field
        else begin
          Loop_verdicts.record (Control_ir.Loop.Function r) Kept;
          field
        end
      | _ -> field )
    fields

(* The definition [d], a function Loopify loopifies of which no loop of
   its own is made here, for the reason [unlowered], with the local
   fixpoints in its body lowered as Loopify lowers those of such a function
   -- the ones translation left for the function's machine to adopt, which
   there is none of to adopt them -- and the outcome Loopify records of it
   recorded. *)
let lower_locals ?unlowered d =
  match function_of d with
  | Some (tparams, ({shape = Definition (params, body); _} as f)) when Table.should_loopify (fst f.path.outer) ->
    let body = Loopify.lower_function_locals ~tparams params body in
    Loopify.record_unlowered ?unlowered f body;
    with_function {f with shape = Definition (params, body)} d
  | Some _ | None -> d

(* [lower] applied to the loop [planned] a function is lowered to, where
   it has one; a function with none is left, no loop made of it. *)
let lowered_or_left lower planned = Option.cata lower (Error (Loopify.Left None)) planned

(* The loop of the helper [r] lifted for the function of a local fixpoint,
   and how it is lowered, where it is one this module lowers: that
   member's. *)
let lifted_loop r =
  match Option.bind (Lifted.of_ref r) Lifted.fixpoint with
  | Some member when Table.should_loopify r ->
    shaped_loop ~lowerings:[Tail; Modulo_cons; Frames] r
      (lowering_of (Recursion_plan.strategy_at ~pointer_fields:Loopify_analysis.constructor_pointer_fields member))
      (Control_ir.Loop.Member (fst member, snd member))
  | Some _ | None -> None

let lifted_resumes r ~owner ~depth ~arity =
  match (owner, lifted_loop r) with
  | Some origin, Some (l, Frames) when Control_ir.Term.entries l.body = [] ->
    (* What the helper captures it takes as its first parameters, passed on
       unchanged by every call, as an invariant parameter is. *)
    let first = depth - arity in
    let invariant = invariant_at l ~first in
    Some (resumes_of ~origin ~depth ~available:(fun b -> b.level < first || invariant b) ~parameters:(first, l) ())
  | _ -> None

let lower_lifted_helper d =
  (* The loop the plan commits the helper to, and what came of it. *)
  let decided =
    match function_of d with
    | None -> None
    | Some (tparams, f) -> (
      match f.shape with
      | Definition (params, _) ->
        Option.map
          (fun ((l : Control_ir.Term.loop), lowering) ->
            ( l.loop,
              lowered_or_left
                (lower_function ~tparams f)
                (Option.map (planned_at l lowering) (lifted_positions l params)) ) )
          (lifted_loop (fst f.path.outer))
      | Declaration _ -> None )
  in
  match decided with
  | Some (loop, Ok f') ->
    Loop_verdicts.record loop Lowered;
    with_function f' d
  | Some (loop, Error unlowered) ->
    Loop_verdicts.record loop (Unlowered (reason unlowered));
    lower_locals ~unlowered d
  | None -> lower_locals d

let lower_group_members decls =
  let loopified d = match Cpp_ir.Globrefs.declared d with Some r -> Option.has_some (planned_loop r) | None -> false in
  List.map
    (fun d ->
      let verdict v =
        match Cpp_ir.Globrefs.declared d with
        | Some r when loopified d -> Loop_verdicts.record (Control_ir.Loop.Function r) v
        | Some _ | None -> ()
      in
      let lowered =
        match function_of d with
        | Some (tparams, f) -> lowered_or_left (lower_function ~tparams f) (planned f)
        | None -> Error (Loopify.Left None)
      in
      match lowered with
      | Ok f ->
        verdict Lowered;
        with_function f d
      | Error unlowered ->
        verdict (Unlowered (reason unlowered));
        lower_locals ~unlowered d )
    decls

(* The entry points: translation still generates MiniCpp, which each
   converts to CppIR on the way in and back on the way out. *)

let local_loop ~owner ~function_ ~lifted ~member ~tparams ~name lam =
  match Legacy_minicpp_to_cpp_ir.lower_expr (Minicpp.CPPlambda lam) with
  | Lambda lam ->
    let tparams = Legacy_minicpp_to_cpp_ir.lower_template_parameters tparams in
    Option.map Cpp_ir_to_legacy_minicpp.stmt (lower_local_loop ~owner ~function_ ~lifted ~member ~tparams ~name lam)
  | _ -> assert false

let lower_methods ~merged inductive vars fields =
  List.map Cpp_ir_to_legacy_minicpp.member
    (lower_struct_methods ~merged inductive vars (List.map Legacy_minicpp_to_cpp_ir.lower_member fields))

let lower_lifted d = Cpp_ir_to_legacy_minicpp.decl (lower_lifted_helper (Legacy_minicpp_to_cpp_ir.lower d))

let lower_group ds =
  List.map Cpp_ir_to_legacy_minicpp.decl (lower_group_members (List.map Legacy_minicpp_to_cpp_ir.lower ds))

(** {1 The control check, over the finished declaration} *)

module Ir = Cpp_ir.Lowered

(* A visit of the children of a node: [expr] for expressions, [stmt] for
   statements, types skipped. *)
let visit ~expr ~stmt : Ir.phase Cpp_ir.Children.visitor = {expr; stmt; type_ = ignore}

(* Whether [stmts], closures' bodies included, make a call of one of the
   occurrences [taken]. *)
let keeps_call taken (stmts : Ir.Stmt.t list) =
  let exception Found in
  let rec v = lazy (visit ~expr:(fun e -> expr e) ~stmt:(fun s -> stmt s))
  and expr (e : Ir.Expr.t) =
    ( match e with
    | Call ({occurrence = Some o; _}, _, _) when List.exists (Miniml.Occurrence.equal o) taken -> raise_notrace Found
    | _ -> () );
    Cpp_ir.Children.expr (Lazy.force v) e
  and stmt s = Cpp_ir.Children.stmt (Lazy.force v) s in
  match List.iter stmt stmts with () -> false | exception Found -> true

(* Whether [stmts], outside every lambda, make a call of one of the
   occurrences [calls] as a whole statement or the value they return or
   bind: one a loop's transform takes where it is one of the loop's turns. *)
let makes_statement_call calls (stmts : Ir.Stmt.t list) =
  let rec bare : Ir.Expr.t -> Ir.Expr.t = function Any_cast (_, e) | Move e -> bare e | e -> e in
  let made e =
    match bare e with
    | Call ({occurrence = Some o; _}, _, _) -> List.exists (Miniml.Occurrence.equal o) calls
    | _ -> false
  in
  let rec stmt (s : Ir.Stmt.t) =
    ( match s with
    | Bind_variable (_, _, e) | Return (Some e) | Expression e -> made e
    | _ -> false )
    ||
    let found = ref false in
    Cpp_ir.Children.stmt (visit ~expr:ignore ~stmt:(fun s -> if not !found then found := stmt s)) s;
    !found
  in
  List.exists stmt stmts

(* The recursive calls of the function of the loop [l], by the Core use
   each is made of. *)
let loop_calls : Control_ir.Loop.t -> Miniml.Occurrence.t list = function
  | Function r -> Loopify.definition_calls r
  | Member (o, m) -> Recursion_plan.member_calls (o, m)

(* The pointer fields of each constructor struct of [s], checked against
   those planned before rendering ({!Loopify_analysis.agree_ptr_fields}). *)
let check_pointer_fields (s : Ir.phase Cpp_ir.Struct.t) =
  let rec fields ((f, _, _) : Ir.phase Cpp_ir.Field.member) =
    match f with
    | Nested_struct (id, sub_fields) ->
      let data =
        List.filter_map
          (fun ((f, _, _) : Ir.phase Cpp_ir.Field.member) -> match f with Data (_, ty) -> Some ty | _ -> None)
          sub_fields
      in
      let pointers =
        List.filter_map Fun.id
          (List.mapi
             (fun i (ty : Ir.Type.t) : Loopify_analysis.ptr_field option ->
               match ty with
               | Shared_pointer (Entity_application (r, _, _)) when Common.globref_equal r s.ref_ -> Some (Recursive i)
               | Shared_pointer _ -> Some (Boxed i)
               | _ -> None )
             data )
      in
      if pointers <> [] then Loopify_analysis.agree_ptr_fields s.ref_ (Id.to_string id) pointers;
      List.iter fields sub_fields
    | _ -> ()
  in
  List.iter fields s.fields

let check_lowered (decl : Ir.Decl.t) =
  let violation (l : Control_ir.Loop.t) what =
    Probe.violation "control lowering"
      Pp.(
        str what ++ str ": "
        ++ match l with Function r -> str (Table.kername_of_global r) | Member _ -> str "a local fixpoint" )
  in
  (* The loop [l], emitted as [body]: a lowering recorded as [recorded]
     allows, no call left of the turns it takes, and no call of its own left
     where it would be a turn -- a statement's whole value -- which its
     ControlIR would have missed. *)
  let emitted l ~recorded body =
    if not (recorded (Loop_verdicts.find l)) then violation l "a loop was emitted that control lowering did not lower";
    if makes_statement_call (loop_calls l) body then
      violation l "a lowered loop still makes a call of its own where it would be a turn";
    match Lower_control.loop l with
    | Some t ->
      if keeps_call (Lower_control.taken_continues t) body then violation l "a lowered loop still makes a call it takes"
    | None -> violation l "a lowered loop has no ControlIR"
  in
  (* The definition of the loop [l], emitted as generated: not lowered, and
     decided on where the plan [committed] it to a loop. *)
  let unlowered l ~committed =
    match Loop_verdicts.find l with
    | Some Lowered -> violation l "a loop control lowering lowered was not emitted"
    | Some (Unlowered why) -> violation l ("a loop the plan commits to was left as generated (" ^ why ^ ")")
    | Some (Declined _ | Kept) -> ()
    | None -> if committed then violation l "the plan commits to a loop control lowering never decided on"
  in
  let lowered = function Some Loop_verdicts.Lowered -> true | Some (Declined _ | Unlowered _ | Kept) | None -> false in
  let function_ (f : Ir.phase Cpp_ir.Function.t) =
    match (f.shape, f.path.inner) with
    | Definition (_, body), [] -> (
      let r = fst f.path.outer in
      match (f.loop, Option.bind (Lifted.of_ref r) Lifted.fixpoint) with
      | Some l, _ -> emitted l ~recorded:lowered body
      | None, Some (o, m) -> unlowered (Member (o, m)) ~committed:(Option.has_some (lifted_loop r))
      | None, None -> unlowered (Function r) ~committed:(Option.has_some (planned_loop r)) )
    | (Definition _ | Declaration _), _ -> ()
  in
  let method_ (m : Ir.phase Cpp_ir.Field.Method.t) =
    match (m.loop, m.globref) with
    | Some l, _ -> emitted l ~recorded:lowered m.body
    | None, Some r -> unlowered (Function r) ~committed:(Option.has_some (method_loop r))
    | None, None -> ()
  in
  (* A local fixpoint lowered with the machine it is in is one control
     lowering kept for that machine. *)
  let fixpoint (l : Ir.phase Cpp_ir.Expr.Lambda.t) =
    match l.fixpoint with
    | Some {member = o, m; encoding = Lowered; _} ->
      emitted (Member (o, m)) l.body ~recorded:(function
        | Some (Loop_verdicts.Lowered | Kept) -> true
        | Some (Declined _ | Unlowered _) | None -> false )
    | Some {member = (o, m) as member; encoding = Self_passing [_]; _} ->
      let committed =
        match Recursion_plan.strategy_at ~pointer_fields:Loopify_analysis.constructor_pointer_fields member with
        | Some (Tail_loop | Modulo_cons _ | Frame_stack) -> true
        | Some (No_loop | Suspended _) | None -> false
      in
      unlowered (Member (o, m)) ~committed
    | Some {encoding = Self_passing _ | Knot; _} | None -> ()
  in
  let rec fields fs =
    List.iter
      (fun ((f, _, _) : Ir.phase Cpp_ir.Field.member) ->
        match f with
        | Method m | Out_of_line_declaration (Method m) -> method_ m
        | Nested_struct (_, fs) -> fields fs
        | _ -> () )
      fs
  in
  let rec decls : Ir.Decl.t -> unit = function
    | Template (_, _, d) -> decls d
    | Namespace (_, ds) -> List.iter decls ds
    | Function f -> function_ f
    | Struct s | Merged_struct_members s ->
      check_pointer_fields s;
      fields s.fields
    | Member_definition {member = Method m; _} -> method_ m
    | _ -> ()
  in
  decls decl;
  let rec v = lazy (visit ~expr:(fun e -> expr e) ~stmt:(fun s -> Cpp_ir.Children.stmt (Lazy.force v) s))
  and expr (e : Ir.Expr.t) =
    (match e with Lambda l -> fixpoint l | _ -> ());
    Cpp_ir.Children.expr (Lazy.force v) e
  in
  Cpp_ir.Children.decl (Lazy.force v) decl
