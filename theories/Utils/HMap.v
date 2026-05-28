From ExtLib Require Import Structures.Reducible.

Section HMaps.

  Context (K : Type) (V : K -> Type).
  Context (map : Type).

  Class HMap : Type :=
  { empty  : map
  ; add    : forall (k : K), V k -> map -> map
  ; remove : K -> map -> map
  ; lookup : forall (k : K), map -> option (V k)
  ; union  : map -> map -> map
  }.

  Class HMapOk (M : HMap) : Type :=
  { mapsto : forall (k : K), V k -> map -> Prop
  ; mapsto_empty : forall k v, ~mapsto k v empty
  ; mapsto_lookup : forall k v m, lookup k m = Some v <-> mapsto k v m
  ; mapsto_add_eq : forall m k v, mapsto k v (add k v m)
  ; mapsto_add_neq : forall m k v k', k <> k' -> forall v', (mapsto k' v' m <-> mapsto k' v' (add k v m))
  ; mapsto_remove_eq : forall m k v, ~ mapsto k v (remove k m)
  ; mapsto_remove_neq : forall m k k', k <> k' -> forall v', (mapsto k' v' m <-> mapsto k' v' (remove k m))
  }.

  Context `{M : HMap}.

  Definition contains (k : K) (m : map) : bool :=
    match lookup k m with
    | None => false
    | Some _ => true
    end.

  Definition singleton (k : K) (v : V k) : map :=
    add k v empty.

  Context {F : Foldable map (sigT V)}.

  Definition combine (f : forall (k : K), V k -> V k -> V k) (m1 m2 : map) : map :=
    fold (fun k_v acc =>
      let '(existT _ k v) := k_v in
      match lookup k acc with
      | None => add k v acc
      | Some v' => add k (f k v v') acc
      end) m2 m1.

  Definition filter (f : forall (k : K), V k -> bool) (m : map) : map :=
    fold (fun k_v acc =>
      let '(existT _ k v) := k_v in
      if f k v
      then add k v acc
      else acc) empty m.

End HMaps.

Arguments empty {_} {_} {_} {_}.
Arguments add {K V} {map} {HMap} _ _ _.
Arguments remove {K V} {map} {HMap} _ _.
Arguments lookup {K V} {map} {HMap} _ _.
Arguments union {K V} {map} {HMap} _ _.
Arguments contains {K V} {map} {M} _ _.
Arguments singleton {K V} {map} {M} _ _.
Arguments combine {K V} {map} {M} _ _ _ _.
Arguments HMapOk {K V} {map} _.