(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
Require Crane.Extraction.
Require Import Crane.Mapping.Std.
From Stdlib Require Import Lists.List Bool.
Import ListNotations.

Module Graph.

Class Eq (A : Type) : Type :=
  { eqb : A -> A -> bool }.

Class Graph (G : Type -> Type) (A : Type) : Type :=
  { edge : Type
  ; empty : G A
  ; add_node : G A -> A -> G A
  ; add_edge : G A -> edge -> G A
  ; nodes    : G A -> list A
  ; edges    : G A -> A -> list edge
  }.

Record DirectedEdge (A : Type) : Type :=
  { edge_from : A
  ; edge_to : A
  }.

Arguments edge_from {A}.
Arguments edge_to {A}.

Definition directed_originates
           {A : Type} `{Eq A} (a : A) (e : DirectedEdge A) : bool := 
  eqb (edge_from e) a.

Record Directed (A : Type) : Type :=
  { directed_nodes : list A
  ; directed_edges : list (DirectedEdge A)
  }.
Arguments directed_nodes {A}.
Arguments directed_edges {A}.

Instance DirectedGraph {A : Type} `{Eq A} : Graph Directed A :=
  { edge := DirectedEdge A

  ; empty := {| directed_nodes := []; directed_edges := [] |}

  ; add_node g n :=
      {| directed_nodes := n :: directed_nodes g
       ; directed_edges := directed_edges g
       |}

  ; add_edge g e :=
      {| directed_nodes := directed_nodes g
       ; directed_edges := e :: directed_edges g
       |}

  ; nodes g   := directed_nodes g
  ; edges g n := filter (directed_originates n) (directed_edges g)
  }.

Record UndirectedEdge (A : Type) : Type :=
  { edge_first : A
  ; edge_second : A
  }.

Arguments edge_first {A}.
Arguments edge_second {A}.

Definition undirected_originates
           {A : Type} `{Eq A} (a : A) (e : UndirectedEdge A) : bool := 
  orb (eqb (edge_first e) a) (eqb (edge_second e) a).

Record Undirected (A : Type) :=
  { undirected_nodes : list A
  ; undirected_edges : list (UndirectedEdge A)
  }.
Arguments undirected_nodes {A}.
Arguments undirected_edges {A}.

Instance UndirectedGraph {A : Type} `{Eq A} : Graph Undirected A :=
  { edge := UndirectedEdge A

  ; empty := {| undirected_nodes := []; undirected_edges := [] |}

  ; add_node g n :=
      {| undirected_nodes := n :: undirected_nodes g
       ; undirected_edges := undirected_edges g
       |}

  ; add_edge g e :=
      {| undirected_nodes := undirected_nodes g
       ; undirected_edges := e :: undirected_edges g
       |}

  ; nodes g   := undirected_nodes g
  ; edges g n := filter (undirected_originates n) (undirected_edges g)
  }.

End Graph.

Crane Extraction "graph" Graph.
