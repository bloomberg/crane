(* The coercion decision ({!Core_to_cpp.Coerce.decide_with}) over a matrix:
   every kind of callable source (a flat global, a curried local, a lambda,
   the value of an immediately invoked lambda, a match or a let, a local
   fixpoint's partial application, a mapping's result) put in every kind of
   slot (a declared parameter, a type-variable parameter, an inline mapping's
   [auto], a loop variable, a frame field, a return, a let, a field, an erased
   slot), at arities 1 to 3.  Types as written, no aliases followed
   ({!Core_to_cpp.Coerce.as_written}). *)

open Crane_plugin
open Names

let leaf i : Cpp_ir.Lowered.Type.t = External (Printf.sprintf "L%d" i, [])

(** The arrows of [n] leaf arguments, flat ([[L1; ...; Ln]]) or curried. *)
let arrows ~flat n : Cpp_ir.Lowered.Arrows.t =
  let doms = List.init n leaf in
  {groups = (if flat then [doms] else List.map (fun d -> [d]) doms); result = leaf 0}

let ty ~flat n = Cpp_ir.Arrows.to_type (arrows ~flat n)
let global = GlobRef.VarRef (Id.of_string "g")

(** A source: its name, its value type, and the grouping it is at ([None]
    for a name, which only an adapter makes a value). *)
type source = {name : string; from : bool -> int -> Cpp_ir.Lowered.Value_type.t; kind : [`Name | `Closure | `Typed]}

let sources =
  [ {name = "flat global"; from = (fun _ n -> Function_name (global, arrows ~flat:true n)); kind = `Name};
    {name = "curried local"; from = (fun _ n -> Typed (ty ~flat:false n)); kind = `Typed};
    {name = "lambda"; from = (fun flat n -> Closure (arrows ~flat n)); kind = `Closure};
    {name = "iife"; from = (fun flat n -> Typed (ty ~flat n)); kind = `Typed};
    {name = "match"; from = (fun flat n -> Typed (ty ~flat n)); kind = `Typed};
    {name = "let"; from = (fun flat n -> Typed (ty ~flat n)); kind = `Typed};
    {name = "fixpoint partial application"; from = (fun flat n -> Closure (arrows ~flat n)); kind = `Closure};
    {name = "mapping result"; from = (fun flat n -> Typed (ty ~flat n)); kind = `Typed} ]

(** A slot: its name and its slot type at arity [n]. *)
let slots : (string * (int -> Cpp_ir.Lowered.Slot_type.t)) list =
  [ ("declared parameter", fun n -> Exactly (ty ~flat:true n));
    ("type-variable parameter", fun n -> Template_parameter (Some (ty ~flat:false n)));
    ("inline mapping auto", fun _ -> Template_parameter None);
    ("loop variable", fun n -> Exactly (ty ~flat:true n));
    ("frame field", fun n -> Exactly (ty ~flat:false n));
    ("return", fun n -> Exactly (ty ~flat:true n));
    ("let", fun _ -> Free);
    ("field", fun n -> Exactly (ty ~flat:false n));
    ("erased", fun _ -> Exactly Any) ]

(** The plan {!Core_to_cpp.Coerce.decide_with} should give, by name: [from]
    at its grouping into [into]. *)
let expected (s : source) (from : Cpp_ir.Lowered.Value_type.t) (into : Cpp_ir.Lowered.Slot_type.t) =
  let grouping : Cpp_ir.Lowered.Value_type.t -> Cpp_ir.Lowered.Arrows.t = function
    | Function_name (_, a) | Closure a -> a
    | Typed t -> Option.get (Cpp_ir.Arrows.of_type t)
    | _ -> assert false
  in
  match (into, s.kind) with
  | (Free | Forwarded | View _ | Join), _ -> "none"
  | Template_parameter _, (`Name | `Closure) -> "name"
  | Template_parameter _, `Typed -> "none"
  | Exactly Any, _ -> "box"
  | Exactly t, _ ->
    let b = Option.get (Cpp_ir.Arrows.of_type t) in
    if Cpp_ir.Arrows.equal (grouping from) b then "none"
    else if s.kind = `Name then "eta"
    else "regroup"

let () =
  let failures = ref 0 in
  List.iter
    (fun n ->
      List.iter
        (fun (s : source) ->
          List.iter
            (fun flat ->
              let from = s.from flat n in
              List.iter
                (fun (slot, into) ->
                  let into = into n in
                  let got =
                    match Core_to_cpp.Coerce.decide_with Core_to_cpp.Coerce.as_written from into with
                    | None -> "none"
                    | Some p -> Cpp_ir.Coercion.decision_name p
                  in
                  let want = expected s from into in
                  if not (String.equal got want) then (
                    incr failures;
                    Printf.eprintf "coercion_decide: %s (%s) into %s at arity %d: got %s, expected %s\n" s.name
                      (if flat then "flat" else "curried") slot n got want ) )
                slots )
            [true; false] )
        sources )
    [1; 2; 3];
  (* A function taking a callable is a template: its name is a value only
     through an adapter, at any grouping. *)
  let higher : Cpp_ir.Lowered.Arrows.t = {groups = [[ty ~flat:true 2]]; result = leaf 0} in
  ( match
      Core_to_cpp.Coerce.decide_with Core_to_cpp.Coerce.as_written (Function_name (global, higher))
        (Exactly (Cpp_ir.Arrows.to_type higher))
    with
    | Some (Eta _) -> ()
    | _ ->
      incr failures;
      prerr_endline "coercion_decide: a global taking a callable, named at its own type, is not eta-expanded" );
  if !failures > 0 then exit 1 else print_endline "coercion_decide: ok"
