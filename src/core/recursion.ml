(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Definitions of a recursive declaration group, and local recursive
    groups ({!Grammar.Recursion}). *)

module Definition = struct
  include Grammar.Recursion.Definition

  (** [fd] with [f] applied to its body. *)
  let map_body f fd = {fd with body = f fd.body}
end

module Member = Grammar.Recursion.Member

module Group = struct
  include Grammar.Recursion.Group

  (** [of_arrays ~selected functions bodies occurrence] is the group whose
      member [i] is named and typed by [functions.(i)] and has the body
      [bodies.(i)]; raises [Invalid_argument] when the two lengths differ, as
      {!make} does. *)
  let of_arrays ~selected functions bodies occurrence =
    make ~selected (Array.map2 (fun (name, type_) body -> {Member.name; type_; body}) functions bodies) occurrence

  (** A group of one member, which it selects. *)
  let singleton name type_ body occurrence = make ~selected:0 [|{Member.name; type_; body}|] occurrence

  let length g = Array.length g.members

  (** Each member's name and type, in binding order. *)
  let functions g = Array.map (fun (m : Member.t) -> (m.name, m.type_)) g.members

  (** Each member's body, in binding order. *)
  let bodies g = Array.map (fun (m : Member.t) -> m.body) g.members

  (** The member the group evaluates to. *)
  let selected_member g = g.members.(g.selected)

  (** [g] with the member [i]'s body [bodies.(i)]; raises
      [Invalid_argument] unless there is one body per member. *)
  let with_bodies g bodies =
    if Array.length bodies <> length g then invalid_arg "Core.Recursion.Group.with_bodies";
    make ~selected:g.selected (Array.map2 (fun (m : Member.t) body -> {m with body}) g.members bodies) g.occurrence

  (** [g] with [f] applied to each body. *)
  let map_bodies f g =
    make ~selected:g.selected (Array.map (fun (m : Member.t) -> {m with body = f m.body}) g.members) g.occurrence

  (** [g] with [h] applied to each body, in order, and then [f] to each
      member's type, in order. *)
  let map f h g =
    let bodies = Array.map (fun (m : Member.t) -> h m.body) g.members in
    let types = Array.map (fun (m : Member.t) -> f m.type_) g.members in
    make ~selected:g.selected
      (Array.mapi (fun i (m : Member.t) -> {m with type_ = types.(i); body = bodies.(i)}) g.members)
      g.occurrence

  (** [g] with [f] applied to each member's name. *)
  let map_names f g =
    make ~selected:g.selected (Array.map (fun (m : Member.t) -> {m with name = f m.name}) g.members) g.occurrence

  (** [g] as a new group, the same but for its occurrence [occurrence]. *)
  let with_occurrence g occurrence = make ~selected:g.selected g.members occurrence
end
