(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Names

type 'p instance = 'p Grammar.Global_use.instance =
  | Monomorphic
  | Polymorphic of 'p Type.at Scheme.Instantiation.t

type 'p at = 'p Grammar.Global_use.at = private {
  callee : GlobRef.t;
  instance : 'p instance;
  occurrence : Occurrence.t;
}

type t = Phase.frozen at
type extracted = Phase.extracted at

let callee g = g.callee
let occurrence g = g.occurrence
let refresh g = Grammar.Global_use.make g.callee g.instance (Occurrence.fresh ())
let monomorphic callee = Grammar.Global_use.make callee Monomorphic (Occurrence.fresh ())

let polymorphic callee inst =
  if Scheme.Id.arity (Scheme.Instantiation.scheme inst) = 0 then monomorphic callee
  else Grammar.Global_use.make callee (Polymorphic inst) (Occurrence.fresh ())

let with_slots callee scheme slot = polymorphic callee (Scheme.Instantiation.make scheme slot)

let infer_all callee scheme =
  with_slots callee scheme (fun _ ->
      {Scheme.solution = Scheme.Type (Type.Hole (Scheme.Hole.fresh ())); source = Scheme.Not_written} )

let identity callee scheme =
  with_slots callee scheme (fun _ -> {Scheme.solution = Scheme.Identity; source = Scheme.Not_written})

let instantiation g =
  match g.instance with
  | Monomorphic -> None
  | Polymorphic inst -> Some inst

let fold_slots f g acc =
  match g.instance with
  | Monomorphic -> acc
  | Polymorphic inst -> Scheme.Instantiation.fold f inst acc

(* What a slot's [Written] evidence stands for in the written list the
   readers were built on: an argument extraction could not read is the
   [Core.Type.Erased] it wrote there. *)
let written_type = function
  | Scheme.Written {observed = Some t; _} -> Some t
  | Scheme.Written {observed = None; _} -> Some (Type.Erased Erasure_reason.Type_argument)
  | Scheme.Not_written -> None

let written_evidence g =
  List.rev
    (fold_slots
       (fun v s acc ->
         match written_type s.Scheme.source with
         | Some t -> (v, t) :: acc
         | None -> acc )
       g [] )

let map_types f g =
  match g.instance with
  | Monomorphic -> g
  | Polymorphic inst -> Grammar.Global_use.make g.callee (Polymorphic (Scheme.Instantiation.map f inst)) g.occurrence

let slot_types g =
  List.rev
    (fold_slots
       (fun _ {Scheme.solution; source} acc ->
         let acc = match solution with Scheme.Type t -> t :: acc | Scheme.Identity -> acc in
         match source with
         | Scheme.Written {observed = Some t; _} -> t :: acc
         | _ -> acc )
       g [] )

let iter_types f g = List.iter f (slot_types g)
let exists_type p g = List.exists p (slot_types g)
