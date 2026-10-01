From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import List.
From CraneTestsRegression Require Import eta_expanded_class_method_param_erased.Cls.
From CraneTestsRegression Require Import eta_expanded_class_method_param_erased.Impl.

(** A class method applied to fewer arguments than it declares, where the class
    parameter the missing one is typed at is the abstract carrier.

    [fun '(x, d) => add x d] gives [add] two of its three arguments.  The call
    resolves to the instance, whose [add] takes [List<std::pair<Nat, Nat>>];
    the missing parameter used to be typed from the {i class}, whose [M] is
    abstract and erases to [std::any]:

      return [=](std::any _sat0) mutable { return map_alist::add(x, d, _sat0); };
      error: no viable conversion from 'std::any' to 'List<std::pair<Nat, Nat>>'

    Nothing distinguished the two sources while the call was saturated,
    because then both sides erase and agree by accident.

    The second half is where the missing parameter is written.  [fold_right]
    takes [(pair, list) -> list], and a parameter synthesised after the
    lambda has been built lands {i inside} it, giving [pair -> (list -> list)]:

      error: no matching member function for call to 'fold_right'

    Seen in Vellvm at [vellvm_bench.h:15411], from
    [Semantics/Handlers/Stack.v:55]:

      let init := List.fold_right (fun '(x,dv) => Maps.add x dv) Maps.empty args *)
Definition build (l : list (nat * nat)) : list (nat * nat) :=
  List.fold_right (fun '(x, d) => add x d) empty l.

(** The control: the same [add], saturated.  Its third argument has a type at
    the call site, so nothing has to be synthesised, and this compiled all
    along. *)
Definition build_saturated (l : list (nat * nat)) : list (nat * nat) :=
  List.fold_right (fun p acc => add (fst p) (snd p) acc) empty l.

Definition apply_it (f : list (nat * nat) -> list (nat * nat))
  (l : list (nat * nat)) : list (nat * nat) := f l.

(** The partial application in an argument position, with no lambda anywhere.
    [build] is no longer a witness for the parameter's {i type}: writing the
    missing binder into the term is what fixed the currying, and a term that
    writes its binders has nothing left to synthesise.  Here there is no
    lambda to write a binder into, so the parameter is still synthesised at
    the C++ level, and still has to be typed from the instance rather than
    from the class. *)
Definition partial (k v : nat) (l : list (nat * nat)) : list (nat * nat) :=
  apply_it (add k v) l.

Crane Extraction "eta_expanded_class_method_param_erased"
  build build_saturated partial.
