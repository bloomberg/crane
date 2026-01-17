(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Corelib Require Import PrimString.
From Crane Require Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.

Module Experiment.
Section Defn.

  Context {E : Type -> Type} {R : Type}.

  Variant itreeF (itree : Type) :=
  | RetF (r : R)
  | TauF (t : itree)
  | VisF {X : Type} (e : E X) (k : X -> itree)
  .

  CoInductive itree : Type := go
  { _observe : itreeF itree }.


  Definition Ret x := (go (RetF itree x)).
  Definition Tau t := (go (TauF itree t)).
  Definition Vis {X} e k := (go (@VisF itree X e k)).

End Defn.


Crane Extract Skip itreeF.
Crane Extract Monad itree [ bind := Vis , ret := Ret ] => "%t1".

Axiom IO : Type -> Type.
Axiom print : string -> IO void.
Axiom print_endline : string -> IO void.
Axiom get_line : IO string.
Axiom read : string -> IO string.

Crane Extract Inlined Constant IO => "%t0".
Crane Extract Inlined Constant print => "std::cout << %a0".
Crane Extract Inlined Constant print_endline => "std::cout << %a0 << '\n'".
Crane Extract Inlined Constant get_line =>
"[]() -> std::string {
    std::string s;
    std::getline(std::cin, s);
    return s;
}()".
Crane Extract Inlined Constant read =>
"[]() -> std::string {
  std::ifstream file(%a0);
  if (!file) {
      std::cerr << ""Failed to open file "" << %a0 << '\n';
      return std::string{};
  }
  return std::string(
      std::istreambuf_iterator<char>(file),
      std::istreambuf_iterator<char>());
}()" From "fstream".


Arguments itree _ _ : clear implicits.
Arguments itreeF _ _ : clear implicits.

End Experiment.

Import Experiment.

Module MonadNotations.

  Declare Scope monad_scope.
  Delimit Scope monad_scope with monad.
  Open Scope monad.

  Notation "e1 ;; e2" := (@Vis _ _ _ e1%monad (fun _ => e2%monad))
    (at level 61, right associativity) : monad_scope.
  Notation "x <- c1 ;; c2" := (@Vis _ _ _ c1%monad (fun x => c2%monad))
    (at level 61, c1 at next level, right associativity) : monad_scope.

End MonadNotations.

Import MonadNotations.

Module TestITree.

  Definition test1 : itree IO void :=
    s <- get_line ;;
    (print_endline s) ;;
    Ret ghost.

  Definition test3 (s : string) : itree IO void :=
    print_endline s ;;
    Ret ghost.

  Definition test4 : itree IO string :=
    print_endline "what is your name?" ;;
    s2 <- get_line ;;
    print_endline (cat "hello " s2) ;;
    Ret (cat "I read the name " (cat s2 " frome the command line!")).

  Definition test5 : itree IO void :=
    s <- read "file.txt" ;;
    print_endline s ;;
    Ret ghost.

End TestITree.


Crane Extraction TestCompile "experiment" TestITree.
