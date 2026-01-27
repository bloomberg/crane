(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Adapted from the Cecoa project: https://github.com/davidnowak/cecoa *)
(* Cecoa has the CeCILL-A license: https://github.com/davidnowak/cecoa/blob/master/LICENSE *)
(* We are not linking to this file in Crane. *)
From Stdlib Require Import PrimString Lists.List Arith.EqNat.

Import ListNotations.
Open Scope pstring_scope.

Require Crane.Extraction.
Require Import Crane.Mapping.Std.
Require Import Crane.Mapping.NatIntStd.

Module ToString.

Definition pair_to_string {A B : Type} (p1 : A -> string) (p2 : B -> string) (x : A * B) : string :=
  match x with
  | (a, b) => cat "(" (cat (p1 a) (cat ", " (cat (p2 b) ")")))
  end.

Fixpoint intersperse {A : Type} (p : A -> string) (sep : string) (l : list A) : string :=
  match l with
  | nil => ""
  | cons z nil => cat sep (p z)
  | cons z l' => cat sep (cat (p z) (intersperse p sep l'))
  end.

Definition list_to_string {A : Type} (p : A -> string) (l : list A) : string :=
  match l with
  | nil => "[]"
  | cons y nil => cat "[" (cat (p y) "]")
  | cons y l' => cat "[" (cat (p y) (cat (intersperse p "; " l') "]"))
  end.

End ToString.

Module TopSort.

Definition entry (node : Type) := (node * list node)%type.
Definition graph (node : Type) := list (entry node).
Definition order (node : Type) := list (list node).

Definition get_elems {node : Type} (eqb_node : node -> node -> bool) (l : list (node * node)) : list node :=
  (fix get_elems_aux (l : list (node * node)) (h : list node) : list node :=
    match l with
    | [] => h
    | (e1, e2) :: l' =>
      let f1 := find (fun x => eqb_node e1 x) h in
      let f2 := find (fun x => eqb_node e2 x) h in
      match (f1, f2) with
      | (None, None) => if eqb_node e1 e2
                            then get_elems_aux l' (e1 :: h)
                            else get_elems_aux l' (e1 :: e2 :: h)
      | (Some x1, None) => get_elems_aux l' (e2 :: h)
      | (None, Some x2) => get_elems_aux l' (e1 :: h)
      | (Some x1, Some x2) => get_elems_aux l' h
      end
    end) l [].

Definition make_entry {node : Type} (eqb_node : node -> node -> bool) (l : list (node * node)) (e : node) : entry node :=
  (e, fold_right (fun x ret => if eqb_node e (fst x) then (snd x) :: ret else ret) [] l).

Definition make_graph {node : Type} (eqb_node : node -> node -> bool) (l : list (node * node)) : graph node :=
  let elems := get_elems eqb_node l in
  fold_right (fun e ret => make_entry eqb_node l e :: ret) [] elems.

Definition graph_lookup {node : Type} (eqb_node : node -> node -> bool) (elem: node) (graph: graph node) : list node :=
  match find (fun entry => eqb_node elem (fst entry)) graph with
  | Some (_, es) => es
  | None => []
  end.

Definition contains {node : Type} (eqb_node : node -> node -> bool) (elem: node) (es: list node) : bool :=
  if find (fun x => eqb_node elem x) es then true else false.

Fixpoint cycle_entry_aux {node : Type} (eqb_node : node -> node -> bool) (graph: graph node) (seens: list node) (elem: node) (counter: nat) : node :=
  if contains eqb_node elem seens then elem else
  match counter with
  | S c => let l := graph_lookup eqb_node elem graph in
           match l with
           | e' :: _ => cycle_entry_aux eqb_node graph (elem :: seens) e' c
           | _ => elem
           end
  | _ => elem
  end.

Definition cycle_entry {node : Type} (eqb_node : node -> node -> bool) (graph : graph node) : option node :=
  match graph with
  | (e, _) :: _ => Some (cycle_entry_aux eqb_node graph [] e (length graph))
  | _ => None
  end.

Fixpoint cycle_extract_aux {node : Type} (eqb_node : node -> node -> bool) (graph: graph node) (counter: nat) (elem: node) (cycl: list node) : list node :=
  match counter with
  | S c =>
    if contains eqb_node elem cycl
    then cycl
    else fold_right (cycle_extract_aux eqb_node graph c)
                    (elem :: cycl)
                    (graph_lookup eqb_node elem graph)
  | _ => cycl
  end.

Definition cycle_extract {node : Type} (eqb_node : node -> node -> bool) (graph: graph node): list node :=
  match cycle_entry eqb_node graph with
  | None => []
  | Some elem => cycle_extract_aux eqb_node graph (length graph) elem []
  end.

Definition null {A: Type} (xs: list A) : bool :=
  if xs then true else false.

Fixpoint topological_sort_aux {node : Type} (eqb_node : node -> node -> bool) (graph: graph node) (counter: nat) : order node :=
  match counter with
    | S c =>
      if null graph
      then []
      else
        let mins := map fst
                        (filter (fun p => null (snd p)) graph) in
        let mins' := if null mins then cycle_extract eqb_node graph else mins in
        let rest := filter (fun entry => negb (contains eqb_node (fst entry) mins')) graph in
        let rest' := map (fun entry => (fst entry, filter (fun e => negb (contains eqb_node e mins')) (snd entry))) rest in
        mins' :: topological_sort_aux eqb_node rest' c
    | _ => []
  end.

Definition topological_sort {node : Type} (eqb_node : node -> node -> bool) (g : list (node * node)) : list (list node) :=
  let g' := make_graph eqb_node g in
  topological_sort_aux eqb_node g' (length g').

Definition topological_sort_graph {node : Type} (eqb_node : node -> node -> bool) (graph : graph node) : order node :=
  topological_sort_aux eqb_node graph (length graph).

Definition topological_rank_list {node : Type} (eqb_node : node -> node -> bool) (graph : graph node) : list (node * nat) :=
  let lorder := topological_sort_graph eqb_node graph in
  concat (map (fun (x: list node * nat) => let (fs, rk) := x in map (fun f => (f, rk)) fs)
              (combine lorder (seq 0 (length lorder)))).


(* Definition test : unit -> string :=
  fun _ => ToString.list_to_string (ToString.list_to_string string_of_nat)
    (TopSort.topological_sort_graph Nat.eqb
      [ (one, [two; three])
      ; (two, [four])
      ; (three, [four; five])
      ; (four, [six])
      ; (five, [six; seven])
      ; (six, [eight])
      ; (seven, [eight; nine])
      ; (eight, [ten])
      ; (nine, [ten; eleven])
      ; (ten, [twelve])
      ; (eleven, [twelve; thirteen])
      ; (twelve, [fourteen])
      ; (thirteen, [fourteen; fifteen])
      ; (fourteen, [sixteen])
      ; (fifteen, [sixteen; seventeen])
      ; (sixteen, [eighteen])
      ; (seventeen, [eighteen; nineteen])
      ; (eighteen, [twenty])
      ; (nineteen, [twenty])
      ; (twenty, []) ]). *)

End TopSort.

(*
Eval compute in (TopSort.topological_sort_graph Nat.eqb [(1, [2]); (2, [])]).
Eval compute in (TopSort.topological_sort_graph Nat.eqb [(1, [2]); (2, [1])]).

Eval compute in (TopSort.topological_sort_graph Nat.eqb
                   [ (1, [2; 3]); (2, [1]); (3, []) ]).

Eval compute in (TopSort.topological_sort_graph Nat.eqb
                   [ (1, [2; 3]); (2, [1]); (3, []); (4, [2; 3])]).
*)

(* Set Crane Format Style "None". *)
Crane Extraction "top" TopSort ToString.

From Stdlib Require Extraction ExtrOcamlBasic ExtrOcamlNatInt.
Extract Constant PrimString.string => "String.t;;
module Pstring = struct
  let unsafe_of_string = fun s -> s
end;;".
Extract Constant PrimString.max_length => "Uint63.of_int 16777211".
Extract Constant PrimString.make => "(fun i c -> let i = Uint63.to_int_min i 16777211 in let c = Uint63.l_and c (Uint63.of_int 255) in let c = Char.chr (Uint63.to_int_min c 255) in String.make i c)".
Extract Constant PrimString.length => "(fun s -> Uint63.of_int (String.length s))".
Extract Constant PrimString.get => "(fun s i -> let i = Uint63.to_int_min i 16777211 in if i < String.length s then Uint63.of_int (Char.code (String.get s i)) else Uint63.zero)".
Extract Constant PrimString.sub => "(fun s off len -> let off = Uint63.to_int_min off max_int in let len = Uint63.to_int_min len max_int in let len_s = String.length s in if off < len_s then String.sub s off (min len (len_s - off)) else """")".
Extract Constant PrimString.cat => "(fun s1 s2 -> let len1 = String.length s1 in let len2 = String.length s2 in if len1 + len2 <= 16777211 then s1 ^ s2 else s1 ^ String.sub s2 0 (16777211 - len1))".
Extract Constant PrimString.compare => "(fun x y -> let c = String.compare x y in if c = 0 then Eq else if c < 0 then Lt else Gt)".

Extract Inlined Constant string_of_nat => "string_of_int".

Definition benchmark : unit -> string :=
  fun _ => ToString.list_to_string (ToString.list_to_string string_of_nat)
    (TopSort.topological_sort_graph Nat.eqb
    [ (one, [two; three])
      ; (two, [four])
      ; (three, [four; five])
      ; (four, [six])
      ; (five, [six; seven])
      ; (six, [eight])
      ; (seven, [eight; nine])
      ; (eight, [ten])
      ; (nine, [ten; eleven])
      ; (ten, [twelve])
      ; (eleven, [twelve; thirteen])
      ; (twelve, [fourteen])
      ; (thirteen, [fourteen; fifteen])
      ; (fourteen, [sixteen])
      ; (fifteen, [sixteen; seventeen])
      ; (sixteen, [eighteen])
      ; (seventeen, [eighteen; nineteen])
      ; (eighteen, [twenty])
      ; (nineteen, [twenty])
      ; (twenty, []) ]).

(* Benchmark feature currently disabled - path resolution issues
Definition benchmark : unit -> string :=
  fun _ =>
    "foo".

Extraction "./top/benchmark/benchmark.ml" benchmark.
Crane Extraction "./top/benchmark/benchmark.cpp" benchmark.

Crane Benchmark benchmark On
  OCaml From "./top/benchmark/benchmark.ml" With "-O1",
  C++ From "./top/benchmark/benchmark.cpp" With "-O1",
  OCaml From "./top/benchmark/benchmark.ml" With "-O2",
  C++ From "./top/benchmark/benchmark.cpp" With "-O2",
  OCaml From "./top/benchmark/benchmark.ml" With "-O3",
  C++ From "./top/benchmark/benchmark.cpp" With "-O3".
*)
