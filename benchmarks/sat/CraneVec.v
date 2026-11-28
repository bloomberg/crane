(** Crane mappings for [SatVec]: each event is a direct call. *)
From Crane Require Extraction.
From Crane Require Import Mapping.Std Mapping.NatInt Monads.ITree.
Require Import SatVec.

From Crane Require Import Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
From Stdlib Require List.
Import PrimString.PStringNotations List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

#[global] Instance vec_mapping (A : Type) : TypeMapping (vec A) :=
  {| type_headers := ["sat_vec.h"];
     type_cpp := Apply "satbench::vec" [TypeArg (SourceType A)];
     type_components := [];
     type_copy := UnknownCopy;
     type_access := ReadOnlyValue ReadByConstReference;
     type_views := NoViews (vec A);
     type_interface := AlgebraicInterface [event (Ref (@mk_vec A)) "satbench::no_loc<%t0>(%a0)"];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.
Crane Extract Skip vecE.
#[global] Instance vmake_mapping : OperationMapping (Ref (@vmake)) :=
  effect_args ["sat_vec.h"] (uses Take ["n"; "x"]) (Structured (Call "satbench::make_vec" [] [Arg "n"; Arg "x"])).
#[global] Instance vget_mapping : OperationMapping (Ref (@vget)) :=
  effect_cpp [] ["v"; "i"] (Structured (Method (Arg "v") "get" [Arg "i"])).
#[global] Instance vset_mapping : OperationMapping (Ref (@vset)) :=
  effect_args [] (uses ReadCanonical ["v"; "i"] ++ uses Take ["x"]) (Structured (Method (Arg "v") "set" [Arg "i"; Arg "x"])).
#[global] Instance vlen_mapping : OperationMapping (Ref (@vlen)) :=
  effect_cpp [] ["v"] (Structured (Method (Arg "v") "len" [])).
#[global] Instance vpush_mapping : OperationMapping (Ref (@vpush)) :=
  effect_args [] (uses ReadCanonical ["v"] ++ uses Take ["x"]) (Structured (Method (Arg "v") "push" [Arg "x"])).
#[global] Instance vshrink_mapping : OperationMapping (Ref (@vshrink)) :=
  effect_cpp [] ["v"; "n"] (Structured (Method (Arg "v") "shrink" [Arg "n"])).
#[global] Instance vabort_mapping : OperationMapping (Ref (@vabort)) :=
  effect_cpp ["sat_vec.h"] ["site"] (Structured (Call "satbench::abort" [TypeParameter "A"] [Arg "site"])).
