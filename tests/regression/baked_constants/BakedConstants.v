(* SPDX-License-Identifier: BSD-3-Clause *)
(** [Crane Bake]: closed constants computed when the command runs and
    extracted as data, under [Set Crane SharedVariant]: a DAG whose shared
    subterms stay shared, a mapped random-access sequence of sequences (static
    blocks), a mapped string and option, and the constants that cannot be
    baked. *)
From Crane Require Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
From Stdlib Require List.
From Crane Require Extraction.
From Crane Require Import Mapping.NatInt.
From Stdlib Require Import List String Ascii.
Import ListNotations.

Set Crane SharedVariant.

Module CharStringMappings.
Import Crane.Mapping.Descriptor Crane.Mapping.Cpp.
Import PrimString.PStringNotations.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

(** [ascii] is a [char]: its eight bits are its fields. *)
#[global] Instance ascii_char_mapping : TypeMapping Ascii.ascii :=
  {| type_headers := [];
     type_cpp := Crane.Cpp.Int Crane.Cpp.Char;
     type_components := [];
     type_copy := BitCopy;
     type_access := ReadOnlyValue ReadByValue;
     type_views := NoViews Ascii.ascii;
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref Ascii.Ascii;
             ctor_build := Expr "(static_cast<char>((%a0 ? 1 : 0) | (%a1 ? 2 : 0) | (%a2 ? 4 : 0) | (%a3 ? 8 : 0) | (%a4 ? 16 : 0) | (%a5 ? 32 : 0) | (%a6 ? 64 : 0) | (%a7 ? 128 : 0)))";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation; case_test := "true";
                       case_fields := [(0, OwnedProjection "static_cast<bool>((%scrut >> 0) & 1)"); (1, OwnedProjection "static_cast<bool>((%scrut >> 1) & 1)"); (2, OwnedProjection "static_cast<bool>((%scrut >> 2) & 1)"); (3, OwnedProjection "static_cast<bool>((%scrut >> 3) & 1)"); (4, OwnedProjection "static_cast<bool>((%scrut >> 4) & 1)"); (5, OwnedProjection "static_cast<bool>((%scrut >> 5) & 1)"); (6, OwnedProjection "static_cast<bool>((%scrut >> 6) & 1)"); (7, OwnedProjection "static_cast<bool>((%scrut >> 7) & 1)")] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

(** [string] is a [std::string] of those characters. *)
#[global] Instance string_std_mapping : TypeMapping String.string :=
  {| type_headers := ["string"];
     type_cpp := Crane.Cpp.Name "std::string";
     type_components := [];
     type_copy := UnknownCopy;
     type_access := ReadOnlyValue ReadByConstReference;
     type_views := NoViews String.string;
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref String.EmptyString;
             ctor_build := Expr "std::string()";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation; case_test := "%scrut.empty()";
                       case_fields := [] |} |};
          {| ctor_source := Ref String.String;
             ctor_build := Expr "std::string(1, %a0) + %a1";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation; case_test := "!%scrut.empty()";
                       case_fields :=
                         [(0, OwnedProjection "%scrut[0]"); (1, OwnedProjection "%scrut.substr(1)")] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.
End CharStringMappings.

Module BakedConstants.

(** A random-access sequence, mapped to [crane::shared_array] as the
    parse-a-lot lexer's tables are. *)
Inductive vec (A : Type) : Type := vnil | vcons (a : A) (v : vec A).
Arguments vnil {A}.
Arguments vcons {A} a v.

Fixpoint vec_of_list {A} (l : list A) : vec A :=
  match l with [] => vnil | x :: xs => vcons x (vec_of_list xs) end.

Fixpoint vec_nth {A} (v : vec A) (n : nat) (d : A) : A :=
  match v, n with
  | vnil, _ => d
  | vcons x _, 0 => x
  | vcons _ v', S m => vec_nth v' m d
  end.

Inductive tree : Type := Leaf | Node (l : tree) (x : nat) (r : tree).

(** [build n] has [2^n - 1] nodes, but only [n] distinct ones: each node's
    two children are one value. *)
Fixpoint build (n : nat) : tree :=
  match n with 0 => Leaf | S m => let t := build m in Node t n t end.

Fixpoint size (t : tree) : nat :=
  match t with Leaf => 0 | Node l _ r => 1 + size l + size r end.

Fixpoint sum_tree (t : tree) : nat :=
  match t with Leaf => 0 | Node l x r => sum_tree l + x + sum_tree r end.

(** Baked: a DAG of 16 nodes standing for 65535. *)
Definition big : tree := build 16.

(** Baked: a table of rows, two of them the same row. *)
Definition row (k : nat) : vec nat := vec_of_list (map (fun i => i * k) (seq 0 10)).
Definition table : vec (vec nat) * vec bool :=
  let r := row 3 in (vec_of_list [row 1; r; r; vnil], vec_of_list [true; false; true]).

(** Baked: a list of labelled records holding strings and options. *)
Record entry : Type := { name : string; weight : option nat; label : tree }.
Definition entries : list entry :=
  [ {| name := "first"; weight := Some 7; label := build 2 |};
    {| name := ""; weight := None; label := Leaf |} ].

Definition big_size (u : unit) : nat := size big.
Definition big_sum (u : unit) : nat := sum_tree big.
Definition cell (i j : nat) : nat := vec_nth (vec_nth (fst table) i vnil) j 0.
Definition accept (i : nat) : bool := vec_nth (snd table) i false.
Definition names (u : unit) : string :=
  fold_right (fun e acc => append (name e) acc) EmptyString entries.
Definition weights (u : unit) : nat :=
  fold_right (fun e acc => match weight e with Some w => w + acc | None => acc end) 0 entries.

(** What cannot be baked. *)
Definition twice (n : nat) : nat := n + n.
Definition a_type : Type := nat.
Record with_fn : Type := { fn : nat -> nat }.
Definition boxed_fn : with_fn := {| fn := twice |}.
CoInductive stream : Type := Cons (hd : nat) (tl : stream).
CoFixpoint ones : stream := Cons 1 ones.
Definition a_proof : 0 = 0 := eq_refl.

End BakedConstants.

Module VecMapping.
Import Crane.Mapping.Descriptor Crane.Mapping.Cpp.
Import PrimString.PStringNotations.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

#[global] Instance vec_mapping (A : Type) : TypeMapping (BakedConstants.vec A) :=
  {| type_headers := ["shared_array.h"];
     type_cpp := Crane.Cpp.Apply "crane::shared_array" [Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "element")];
     type_components :=
       [{| component_name := "element"; component_type := FieldType (Ref (@BakedConstants.vcons A)) 0 |}];
     type_copy := UnknownCopy;
     type_access := ReadOnlyValue ReadByConstReference;
     type_views := NoViews (BakedConstants.vec A);
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref (@BakedConstants.vnil A);
             ctor_build := Expr "crane::shared_array<%stored(element)>{}";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation;
                       case_test := "%scrut.empty()"; case_fields := [] |} |};
          {| ctor_source := Ref (@BakedConstants.vcons A);
             ctor_build := Expr "%a1.push_front(%a0)";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation;
                       case_test := "!%scrut.empty()";
                       case_fields :=
                         [(0, CanonicalBorrowProjection "%scrut.front()");
                          (1, OwnedProjection "%scrut.drop(1)")] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.
End VecMapping.

Import Crane.Mapping.Descriptor Crane.Mapping.Cpp.
Import PrimString.PStringNotations.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

#[global] Instance vec_nth_mapping : OperationMapping (Ref (@BakedConstants.vec_nth)) :=
  pure_cpp [] ["v"; "n"; "d"]
    (Expr "(static_cast<std::size_t>(%arg(n)) < (%arg(v)).size() ? (%arg(v))[static_cast<std::size_t>(%arg(n))] : %arg(d))").

Crane Bake BakedConstants.big BakedConstants.table BakedConstants.entries.

Fail Crane Bake BakedConstants.twice.
Fail Crane Bake BakedConstants.a_type.
Fail Crane Bake BakedConstants.boxed_fn.
Fail Crane Bake BakedConstants.ones.
Fail Crane Bake BakedConstants.a_proof.
Fail Crane Bake BakedConstants.tree.

Crane Extraction "baked_constants" BakedConstants.
