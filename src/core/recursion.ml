(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** [Core.Recursion]: the definitions of a top-level recursive declaration
    group ([Core.Decl.Recursive_group]), and local recursive groups (the
    payload of [Core.Expr.Fixpoint] and [Core.Expr.Cofixpoint]). *)

(** One definition of a top-level recursive group. *)
module Definition = struct
  include Grammar.Recursion.Definition

  type t = Phase.frozen at
  type extracted = Phase.extracted at

  (** [fd] with [f] applied to its body. *)
  let map_body f fd = {fd with body = f fd.body}
end

(** One function of a local recursive group: name, type and body. *)
module Member = struct
  include Grammar.Recursion.Member

  type t = Phase.frozen at
  type extracted = Phase.extracted at
end

(** A local recursive group: its members, the one selected, and its
    occurrence; built only through {!make} and the functions here. *)
module Group = struct
  include Grammar.Recursion.Group

  type t = Phase.frozen at
  type extracted = Phase.extracted at

  (** [of_arrays ~selected functions bodies occurrence] is the group whose
      member [i] is named and typed by [functions.(i)] and has the body
      [bodies.(i)]; raises [Invalid_argument] when the two lengths differ, as
      {!make} does. *)
  let of_arrays ~selected functions bodies occurrence =
    make ~selected (Array.map2 (fun (name, type_) body -> {Member.name; type_; body}) functions bodies) occurrence

  (** A group of one member, which it selects. *)
  let singleton name type_ body occurrence = make ~selected:0 [|{Member.name; type_; body}|] occurrence

  (** The number of members. *)
  let length g = Array.length g.members

  (** Each member's name and type, in binding order. *)
  let functions g = Array.map (fun (m : _ Member.at) -> (m.name, m.type_)) g.members

  (** Each member's body, in binding order. *)
  let bodies g = Array.map (fun (m : _ Member.at) -> m.body) g.members

  (** The member the group evaluates to. *)
  let selected_member g = g.members.(g.selected)

  (** [g] with the member [i]'s body [bodies.(i)]; raises
      [Invalid_argument] unless there is one body per member. *)
  let with_bodies g bodies =
    if Array.length bodies <> length g then invalid_arg "Core.Recursion.Group.with_bodies";
    make ~selected:g.selected (Array.map2 (fun (m : _ Member.at) body -> {m with body}) g.members bodies) g.occurrence

  (** [g] with [f] applied to each body. *)
  let map_bodies f g =
    make ~selected:g.selected (Array.map (fun (m : _ Member.at) -> {m with body = f m.body}) g.members) g.occurrence

  (** [g] with [h] applied to each body, in order, and then [f] to each
      member's type, in order. *)
  let map f h g =
    let bodies = Array.map (fun (m : _ Member.at) -> h m.body) g.members in
    let types = Array.map (fun (m : _ Member.at) -> f m.type_) g.members in
    make ~selected:g.selected
      (Array.mapi (fun i (m : _ Member.at) -> {m with type_ = types.(i); body = bodies.(i)}) g.members)
      g.occurrence

  (** [g] with [f] applied to each member's name. *)
  let map_names f g =
    make ~selected:g.selected (Array.map (fun (m : _ Member.at) -> {m with name = f m.name}) g.members) g.occurrence

  (** [g] as a new group, the same but for its occurrence [occurrence]. *)
  let with_occurrence g occurrence = make ~selected:g.selected g.members occurrence
end
