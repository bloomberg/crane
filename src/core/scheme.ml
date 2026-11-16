(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

module Id = struct
  type t = {
    stamp : int;
    owner : Names.GlobRef.t;
    arity : int;
  }

  let counter = ref 0

  let fresh owner ~arity =
    incr counter;
    {stamp = !counter; owner; arity}

  let owner id = id.owner
  let arity id = id.arity
  let equal a b = Int.equal a.stamp b.stamp

  let pp id =
    Pp.(
      str "scheme#" ++ int id.stamp ++ str "("
      ++ Names.GlobRef.print id.owner
      ++ str "/" ++ int id.arity ++ str ")")
end

module Var = struct
  type t = {
    owner : Id.t;
    ordinal : int;
  }

  let owner v = v.owner
  let ordinal v = v.ordinal

  let of_tvar owner i =
    if 1 <= i && i <= Id.arity owner then Some {owner; ordinal = i} else None

  let all owner = List.init (Id.arity owner) (fun i -> {owner; ordinal = i + 1})
  let equal a b = Id.equal a.owner b.owner && Int.equal a.ordinal b.ordinal

  let compare a b =
    match Int.compare a.owner.Id.stamp b.owner.Id.stamp with
    | 0 -> Int.compare a.ordinal b.ordinal
    | c -> c

  let assoc_opt v l = List.find_map (fun (w, x) -> if equal v w then Some x else None) l

  let assoc_tvar i l =
    match l with
    | [] -> None
    | (w, _) :: _ -> Option.bind (of_tvar w.owner i) (fun v -> assoc_opt v l)
  let pp var = Pp.(Id.pp var.owner ++ str "." ++ int var.ordinal)
end

module Binder = struct
  type t = int

  let of_position p =
    if p < 0 then invalid_arg "Scheme.Binder.of_position" else p

  let position b = b
  let equal = Int.equal
  let pp b = Pp.(str "binder#" ++ int b)
end

module Hole = struct
  let last = ref 0

  let fresh () =
    incr last;
    !last
end

type 'ty solution =
  | Identity
  | Type of 'ty

type 'ty source_evidence =
  | Not_written
  | Written of {
      binder : Binder.t;
      observed : 'ty option;
    }

type 'ty slot = {
  solution : 'ty solution;
  source : 'ty source_evidence;
}

module Instantiation = struct
  type 'ty t = {
    scheme : Id.t;
    slots : 'ty slot array;
  }

  let make scheme f =
    {scheme; slots = Array.of_list (List.map f (Var.all scheme))}

  let scheme i = i.scheme

  let index i v =
    if not (Id.equal (Var.owner v) i.scheme) then
      invalid_arg "Scheme.Instantiation: a variable of another scheme";
    Var.ordinal v - 1

  let slot i v = i.slots.(index i v)

  let map_solution f = function
    | Identity -> Identity
    | Type t -> Type (f t)

  let map_source f = function
    | Not_written -> Not_written
    | Written {binder; observed} ->
      Written {binder; observed = Option.map f observed}

  let map f i =
    { i with
      slots =
        Array.map
          (fun s -> {solution = map_solution f s.solution; source = map_source f s.source})
          i.slots }

  let var i k = {Var.owner = i.scheme; ordinal = k + 1}
  let map_slots f i = {i with slots = Array.mapi (fun k s -> f (var i k) s) i.slots}

  let fold f i acc =
    let rec go k acc =
      if k = Array.length i.slots then acc else go (k + 1) (f (var i k) i.slots.(k) acc)
    in
    go 0 acc

  let for_all p i = fold (fun v s ok -> ok && p v s) i true
  let exists p i = fold (fun v s found -> found || p v s) i false
end
