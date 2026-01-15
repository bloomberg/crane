(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Adapted from the Cecoa project: https://github.com/davidnowak/cecoa *)
(* Cecoa has the CeCILL-A license: https://github.com/davidnowak/cecoa/blob/master/LICENSE *)
(* We are not linking to this file in Crane. *)
From Stdlib Require Import PrimString Lists.List Arith.EqNat.

Import ListNotations.
Open Scope pstring_scope.

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

End TopSort.

(*
Eval compute in (TopSort.topological_sort_graph Nat.eqb [(1, [2]); (2, [])]).
Eval compute in (TopSort.topological_sort_graph Nat.eqb [(1, [2]); (2, [1])]).

Eval compute in (TopSort.topological_sort_graph Nat.eqb
                   [ (1, [2; 3]); (2, [1]); (3, []) ]).

Eval compute in (TopSort.topological_sort_graph Nat.eqb
                   [ (1, [2; 3]); (2, [1]); (3, []); (4, [2; 3])]).
*)

Require Crane.Extraction.

Set Crane BDE Directory "~/bde_install/".
From Crane Require Import Mapping.BDE Mapping.NatIntBDE.
Crane Extraction TestCompile "top_bde" TopSort ToString.

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

Definition bigDAG := [
  (one, [two; three]) ;
  (two, [three; four]) ;
  (three, [four; five]) ;
  (four, [five; six]) ;
  (five, [six; seven; ten]) ;
  (six, [seven; eight]) ;
  (seven, [eight; nine; fourteen]) ;
  (eight, [nine; ten]) ;
  (nine, [ten; eleven]) ;
  (ten, [eleven; twelve; fifteen]) ;
  (eleven, [twelve; thirteen; twenty_two]) ;
  (twelve, [thirteen; fourteen]) ;
  (thirteen, [fourteen; fifteen]) ;
  (fourteen, [fifteen; sixteen; twenty_one]) ;
  (fifteen, [sixteen; seventeen; twenty]) ;
  (sixteen, [seventeen; eighteen]) ;
  (seventeen, [eighteen; nineteen; twenty_four]) ;
  (eighteen, [nineteen; twenty]) ;
  (nineteen, [twenty; twenty_one]) ;
  (twenty, [twenty_one; twenty_two; twenty_five]) ;
  (twenty_one, [twenty_two; twenty_three]) ;
  (twenty_two, [twenty_three; twenty_four; thirty_three]) ;
  (twenty_three, [twenty_four; twenty_five]) ;
  (twenty_four, [twenty_five; twenty_six]) ;
  (twenty_five, [twenty_six; twenty_seven; thirty]) ;
  (twenty_six, [twenty_seven; twenty_eight]) ;
  (twenty_seven, [twenty_eight; twenty_nine; thirty_four]) ;
  (twenty_eight, [twenty_nine; thirty]) ;
  (twenty_nine, [thirty; thirty_one]) ;
  (thirty, [thirty_one; thirty_two; thirty_five]) ;
  (thirty_one, [thirty_two; thirty_three]) ;
  (thirty_two, [thirty_three; thirty_four]) ;
  (thirty_three, [thirty_four; thirty_five; forty_four]) ;
  (thirty_four, [thirty_five; thirty_six]) ;
  (thirty_five, [thirty_six; thirty_seven; forty]) ;
  (thirty_six, [thirty_seven; thirty_eight]) ;
  (thirty_seven, [thirty_eight; thirty_nine; forty_six]) ;
  (thirty_eight, [thirty_nine; forty]) ;
  (thirty_nine, [forty; forty_one]) ;
  (forty, [forty_one; forty_two; forty_five]) ;
  (forty_one, [forty_two; forty_three]) ;
  (forty_two, [forty_three; forty_four]) ;
  (forty_three, [forty_four; forty_five]) ;
  (forty_four, [forty_five; forty_six; fifty_five]) ;
  (forty_five, [forty_six; forty_seven; fifty]) ;
  (forty_six, [forty_seven; forty_eight; fifty_three]) ;
  (forty_seven, [forty_eight; forty_nine]) ;
  (forty_eight, [forty_nine; fifty]) ;
  (forty_nine, [fifty; fifty_one]) ;
  (fifty, [fifty_one; fifty_two; fifty_five]) ;
  (fifty_one, [fifty_two; fifty_three]) ;
  (fifty_two, [fifty_three; fifty_four]) ;
  (fifty_three, [fifty_four; fifty_five; sixty_four]) ;
  (fifty_four, [fifty_five; fifty_six]) ;
  (fifty_five, [fifty_six; fifty_seven; sixty]) ;
  (fifty_six, [fifty_seven; fifty_eight]) ;
  (fifty_seven, [fifty_eight; fifty_nine; sixty_six]) ;
  (fifty_eight, [fifty_nine; sixty]) ;
  (fifty_nine, [sixty; sixty_one]) ;
  (sixty, [sixty_one; sixty_two; sixty_five]) ;
  (sixty_one, [sixty_two; sixty_three]) ;
  (sixty_two, [sixty_three; sixty_four]) ;
  (sixty_three, [sixty_four; sixty_five]) ;
  (sixty_four, [sixty_five; sixty_six; seventy_five]) ;
  (sixty_five, [sixty_six; sixty_seven; seventy]) ;
  (sixty_six, [sixty_seven; sixty_eight]) ;
  (sixty_seven, [sixty_eight; sixty_nine; seventy_four]) ;
  (sixty_eight, [sixty_nine; seventy]) ;
  (sixty_nine, [seventy; seventy_one]) ;
  (seventy, [seventy_one; seventy_two; seventy_five]) ;
  (seventy_one, [seventy_two; seventy_three]) ;
  (seventy_two, [seventy_three; seventy_four]) ;
  (seventy_three, [seventy_four; seventy_five]) ;
  (seventy_four, [seventy_five; seventy_six; eighty_five]) ;
  (seventy_five, [seventy_six; seventy_seven; eighty]) ;
  (seventy_six, [seventy_seven; seventy_eight]) ;
  (seventy_seven, [seventy_eight; seventy_nine; eighty_four]) ;
  (seventy_eight, [seventy_nine; eighty]) ;
  (seventy_nine, [eighty; eighty_one]) ;
  (eighty, [eighty_one; eighty_two; eighty_five]) ;
  (eighty_one, [eighty_two; eighty_three]) ;
  (eighty_two, [eighty_three; eighty_four]) ;
  (eighty_three, [eighty_four; eighty_five]) ;
  (eighty_four, [eighty_five; eighty_six; ninety_five]) ;
  (eighty_five, [eighty_six; eighty_seven; ninety]) ;
  (eighty_six, [eighty_seven; eighty_eight]) ;
  (eighty_seven, [eighty_eight; eighty_nine; ninety_four]) ;
  (eighty_eight, [eighty_nine; ninety]) ;
  (eighty_nine, [ninety; ninety_one]) ;
  (ninety, [ninety_one; ninety_two; ninety_five]) ;
  (ninety_one, [ninety_two; ninety_three]) ;
  (ninety_two, [ninety_three; ninety_four]) ;
  (ninety_three, [ninety_four; ninety_five]) ;
  (ninety_four, [ninety_five; ninety_six; one_hundred_five]) ;
  (ninety_five, [ninety_six; ninety_seven; one_hundred]) ;
  (ninety_six, [ninety_seven; ninety_eight]) ;
  (ninety_seven, [ninety_eight; ninety_nine; one_hundred_four]) ;
  (ninety_eight, [ninety_nine; one_hundred]) ;
  (ninety_nine, [one_hundred; one_hundred_one]) ;
  (one_hundred, [one_hundred_one; one_hundred_two; one_hundred_five]) ;
  (one_hundred_one, [one_hundred_two; one_hundred_three]) ;
  (one_hundred_two, [one_hundred_three; one_hundred_four]) ;
  (one_hundred_three, [one_hundred_four; one_hundred_five]) ;
  (one_hundred_four, [one_hundred_five; one_hundred_six; one_hundred_fifteen]) ;
  (one_hundred_five, [one_hundred_six; one_hundred_seven; one_hundred_ten]) ;
  (one_hundred_six, [one_hundred_seven; one_hundred_eight]) ;
  (one_hundred_seven, [one_hundred_eight; one_hundred_nine; one_hundred_fourteen]) ;
  (one_hundred_eight, [one_hundred_nine; one_hundred_ten]) ;
  (one_hundred_nine, [one_hundred_ten; one_hundred_eleven]) ;
  (one_hundred_ten, [one_hundred_eleven; one_hundred_twelve; one_hundred_fifteen]) ;
  (one_hundred_eleven, [one_hundred_twelve; one_hundred_thirteen; one_hundred_twenty_two]) ;
  (one_hundred_twelve, [one_hundred_thirteen; one_hundred_fourteen]) ;
  (one_hundred_thirteen, [one_hundred_fourteen; one_hundred_fifteen]) ;
  (one_hundred_fourteen, [one_hundred_fifteen; one_hundred_sixteen; one_hundred_twenty_one]) ;
  (one_hundred_fifteen, [one_hundred_sixteen; one_hundred_seventeen; one_hundred_twenty]) ;
  (one_hundred_sixteen, [one_hundred_seventeen; one_hundred_eighteen]) ;
  (one_hundred_seventeen, [one_hundred_eighteen; one_hundred_nineteen; one_hundred_twenty_four]) ;
  (one_hundred_eighteen, [one_hundred_nineteen; one_hundred_twenty]) ;
  (one_hundred_nineteen, [one_hundred_twenty; one_hundred_twenty_one]) ;
  (one_hundred_twenty, [one_hundred_twenty_one; one_hundred_twenty_two; one_hundred_twenty_five]) ;
  (one_hundred_twenty_one, [one_hundred_twenty_two; one_hundred_twenty_three]) ;
  (one_hundred_twenty_two, [one_hundred_twenty_three; one_hundred_twenty_four; one_hundred_thirty_three]) ;
  (one_hundred_twenty_three, [one_hundred_twenty_four; one_hundred_twenty_five]) ;
  (one_hundred_twenty_four, [one_hundred_twenty_five; one_hundred_twenty_six]) ;
  (one_hundred_twenty_five, [one_hundred_twenty_six; one_hundred_twenty_seven; one_hundred_thirty]) ;
  (one_hundred_twenty_six, [one_hundred_twenty_seven; one_hundred_twenty_eight]) ;
  (one_hundred_twenty_seven, [one_hundred_twenty_eight; one_hundred_twenty_nine; one_hundred_thirty_four]) ;
  (one_hundred_twenty_eight, [one_hundred_twenty_nine; one_hundred_thirty]) ;
  (one_hundred_twenty_nine, [one_hundred_thirty; one_hundred_thirty_one]) ;
  (one_hundred_thirty, [one_hundred_thirty_one; one_hundred_thirty_two; one_hundred_thirty_five]) ;
  (one_hundred_thirty_one, [one_hundred_thirty_two; one_hundred_thirty_three]) ;
  (one_hundred_thirty_two, [one_hundred_thirty_three; one_hundred_thirty_four]) ;
  (one_hundred_thirty_three, [one_hundred_thirty_four; one_hundred_thirty_five; one_hundred_forty_four]) ;
  (one_hundred_thirty_four, [one_hundred_thirty_five; one_hundred_thirty_six]) ;
  (one_hundred_thirty_five, [one_hundred_thirty_six; one_hundred_thirty_seven; one_hundred_forty]) ;
  (one_hundred_thirty_six, [one_hundred_thirty_seven; one_hundred_thirty_eight]) ;
  (one_hundred_thirty_seven, [one_hundred_thirty_eight; one_hundred_thirty_nine]) ;
  (one_hundred_thirty_eight, [one_hundred_thirty_nine; one_hundred_forty]) ;
  (one_hundred_thirty_nine, [one_hundred_forty; one_hundred_forty_one]) ;
  (one_hundred_forty, [one_hundred_forty_one; one_hundred_forty_two; one_hundred_forty_five; one_hundred_forty_seven]) ;
  (one_hundred_forty_one, [one_hundred_forty_two; one_hundred_forty_three]) ;
  (one_hundred_forty_two, [one_hundred_forty_three; one_hundred_forty_four]) ;
  (one_hundred_forty_three, [one_hundred_forty_four; one_hundred_forty_five]) ;
  (one_hundred_forty_four, [one_hundred_forty_five; one_hundred_forty_six]) ;
  (one_hundred_forty_five, [one_hundred_forty_six; one_hundred_forty_seven; one_hundred_fifty]) ;
  (one_hundred_forty_six, [one_hundred_forty_seven; one_hundred_forty_eight]) ;
  (one_hundred_forty_seven, [one_hundred_forty_eight; one_hundred_forty_nine]) ;
  (one_hundred_forty_eight, [one_hundred_forty_nine; one_hundred_fifty]) ;
  (one_hundred_forty_nine, [one_hundred_fifty]) ;
  (one_hundred_fifty, [])
].


Definition benchmark : unit -> string :=
  fun _ =>
  ToString.list_to_string (ToString.list_to_string string_of_nat)
    (TopSort.topological_sort_graph Nat.eqb bigDAG).

(* Definition benchmark : unit -> string :=
  fun _ =>
    "foo". *)

Extraction "./top_bde/benchmark/benchmark.ml" benchmark.
Crane Extraction "./top_bde/benchmark/benchmark.cpp" benchmark.

Crane Benchmark benchmark On
  OCaml From "./top_bde/benchmark/benchmark.ml" With "-O1",
  C++ From "./top_bde/benchmark/benchmark.cpp" With "-O1",
  OCaml From "./top_bde/benchmark/benchmark.ml" With "-O2",
  C++ From "./top_bde/benchmark/benchmark.cpp" With "-O2",
  OCaml From "./top_bde/benchmark/benchmark.ml" With "-O3",
  C++ From "./top_bde/benchmark/benchmark.cpp" With "-O3".
