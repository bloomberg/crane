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

Module TopologicalSort.

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

End TopologicalSort.

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
Crane Extraction "topological_sort_bde" TopologicalSort ToString.

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
  (1, [2; 3]) ;
  (2, [3; 4]) ;
  (3, [4; 5]) ;
  (4, [5; 6]) ;
  (5, [6; 7; 10]) ;
  (6, [7; 8]) ;
  (7, [8; 9; 14]) ;
  (8, [9; 10]) ;
  (9, [10; 11]) ;
  (10, [11; 12; 15]) ;
  (11, [12; 13; 22]) ;
  (12, [13; 14]) ;
  (13, [14; 15]) ;
  (14, [15; 16; 21]) ;
  (15, [16; 17; 20]) ;
  (16, [17; 18]) ;
  (17, [18; 19; 24]) ;
  (18, [19; 20]) ;
  (19, [20; 21]) ;
  (20, [21; 22; 25]) ;
  (21, [22; 23]) ;
  (22, [23; 24; 33]) ;
  (23, [24; 25]) ;
  (24, [25; 26]) ;
  (25, [26; 27; 30]) ;
  (26, [27; 28]) ;
  (27, [28; 29; 34]) ;
  (28, [29; 30]) ;
  (29, [30; 31]) ;
  (30, [31; 32; 35]) ;
  (31, [32; 33]) ;
  (32, [33; 34]) ;
  (33, [34; 35; 44]) ;
  (34, [35; 36]) ;
  (35, [36; 37; 40]) ;
  (36, [37; 38]) ;
  (37, [38; 39; 46]) ;
  (38, [39; 40]) ;
  (39, [40; 41]) ;
  (40, [41; 42; 45]) ;
  (41, [42; 43]) ;
  (42, [43; 44]) ;
  (43, [44; 45]) ;
  (44, [45; 46; 55]) ;
  (45, [46; 47; 50]) ;
  (46, [47; 48; 53]) ;
  (47, [48; 49]) ;
  (48, [49; 50]) ;
  (49, [50; 51]) ;
  (50, [51; 52; 55]) ;
  (51, [52; 53]) ;
  (52, [53; 54]) ;
  (53, [54; 55; 64]) ;
  (54, [55; 56]) ;
  (55, [56; 57; 60]) ;
  (56, [57; 58]) ;
  (57, [58; 59; 66]) ;
  (58, [59; 60]) ;
  (59, [60; 61]) ;
  (60, [61; 62; 65]) ;
  (61, [62; 63]) ;
  (62, [63; 64]) ;
  (63, [64; 65]) ;
  (64, [65; 66; 75]) ;
  (65, [66; 67; 70]) ;
  (66, [67; 68]) ;
  (67, [68; 69; 74]) ;
  (68, [69; 70]) ;
  (69, [70; 71]) ;
  (70, [71; 72; 75]) ;
  (71, [72; 73]) ;
  (72, [73; 74]) ;
  (73, [74; 75]) ;
  (74, [75; 76; 85]) ;
  (75, [76; 77; 80]) ;
  (76, [77; 78]) ;
  (77, [78; 79; 84]) ;
  (78, [79; 80]) ;
  (79, [80; 81]) ;
  (80, [81; 82; 85]) ;
  (81, [82; 83]) ;
  (82, [83; 84]) ;
  (83, [84; 85]) ;
  (84, [85; 86; 95]) ;
  (85, [86; 87; 90]) ;
  (86, [87; 88]) ;
  (87, [88; 89; 94]) ;
  (88, [89; 90]) ;
  (89, [90; 91]) ;
  (90, [91; 92; 95]) ;
  (91, [92; 93]) ;
  (92, [93; 94]) ;
  (93, [94; 95]) ;
  (94, [95; 96; 105]) ;
  (95, [96; 97; 100]) ;
  (96, [97; 98]) ;
  (97, [98; 99; 104]) ;
  (98, [99; 100]) ;
  (99, [100; 101]) ;
  (100, [101; 102; 105]) ;
  (101, [102; 103]) ;
  (102, [103; 104]) ;
  (103, [104; 105]) ;
  (104, [105; 106; 115]) ;
  (105, [106; 107; 110]) ;
  (106, [107; 108]) ;
  (107, [108; 109; 114]) ;
  (108, [109; 110]) ;
  (109, [110; 111]) ;
  (110, [111; 112; 115]) ;
  (111, [112; 113; 122]) ;
  (112, [113; 114]) ;
  (113, [114; 115]) ;
  (114, [115; 116; 121]) ;
  (115, [116; 117; 120]) ;
  (116, [117; 118]) ;
  (117, [118; 119; 124]) ;
  (118, [119; 120]) ;
  (119, [120; 121]) ;
  (120, [121; 122; 125]) ;
  (121, [122; 123]) ;
  (122, [123; 124; 133]) ;
  (123, [124; 125]) ;
  (124, [125; 126]) ;
  (125, [126; 127; 130]) ;
  (126, [127; 128]) ;
  (127, [128; 129; 134]) ;
  (128, [129; 130]) ;
  (129, [130; 131]) ;
  (130, [131; 132; 135]) ;
  (131, [132; 133]) ;
  (132, [133; 134]) ;
  (133, [134; 135; 144]) ;
  (134, [135; 136]) ;
  (135, [136; 137; 140]) ;
  (136, [137; 138]) ;
  (137, [138; 139]) ;
  (138, [139; 140]) ;
  (139, [140; 141]) ;
  (140, [141; 142; 145; 147]) ;
  (141, [142; 143]) ;
  (142, [143; 144]) ;
  (143, [144; 145]) ;
  (144, [145; 146]) ;
  (145, [146; 147; 150]) ;
  (146, [147; 148]) ;
  (147, [148; 149]) ;
  (148, [149; 150]) ;
  (149, [150]) ;
  (150, [])
].


(* Benchmark feature currently disabled - path resolution issues
Definition benchmark : unit -> string :=
  fun _ =>
  ToString.list_to_string (ToString.list_to_string string_of_nat)
    (TopSort.topological_sort_graph Nat.eqb bigDAG).

Extraction "./benchmark/benchmark.ml" benchmark.
Crane Extraction "./benchmark/benchmark.cpp" benchmark.

Crane Benchmark benchmark On
  OCaml From "./benchmark/benchmark.ml" With "-O1",
  C++ From "./benchmark/benchmark.cpp" With "-O1",
  OCaml From "./benchmark/benchmark.ml" With "-O2",
  C++ From "./benchmark/benchmark.cpp" With "-O2",
  OCaml From "./benchmark/benchmark.ml" With "-O3",
  C++ From "./benchmark/benchmark.cpp" With "-O3".
*)
