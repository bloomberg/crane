(* A higher-kinded parameter abstracting over an event family has nothing it
   can ever be passed, because event families are not emitted as templates.

   This is 24 of Vellvm's 31 remaining errors (`raiseUB`, `raiseLLVM`,
   `raise`, `raiseOOM`), reproduced here as a single error:

     std::shared_ptr<ITree<T2>> trigger_cast_(T1<Void0> e);   // T1 a template

     template <typename T1 = void, typename T2>
     static std::shared_ptr<ITree<T2>> raiseUB() {
       return trigger_cast_<std::any, T2>(UBE::throwub(std::monostate{}));
     }

     error: invalid explicitly-specified argument for template parameter 'T1'

   Three things have to hold together, and each was a wrong turn on the way:

   1. **The dictionary is skipped, not merely unused.**  Crane's ITree mapping
      has `Crane Extract Skip ReSum.` and `subevent => "%a0"`, so the
      `` `{UBE -< E} `` parameter's *type* is erased and `E` loses its last
      occurrence in the emitted signature.  With an ordinary user class the
      parameter survives and an arity can be read off it -- that is the
      neighbouring test `subevent_forward_loses_kind`, and it is a different
      defect.

   2. **The callee keeps the higher kind only because its codomain is an
      itree.**  With `list B` as the result, `trigger_cast'` demotes to
      `typename` and the whole thing compiles.  `itree E A` names `E` and then
      drops it on the way to `ITree<A>`, and that is what leaves the parameter
      higher-kinded.  Both earlier reduction attempts used `list B` and so
      could not reproduce this.

   3. **The event family must be index-based with constructors at differing
      indices.**  `UBE (A : Type)` comes out `template <typename A> struct UBE`
      -- a real template, which *could* satisfy the position, making the defect
      merely that the call spells `std::any` instead of `UBE`.  Vellvm's
      families are declared `UBE : Type -> Type` with several constructors at
      different indices, which emits a plain `struct UBE`.  Then there is no
      template in the program to pass, and `std::any` is not a lost template
      but a placeholder for one that was never going to exist.

   So the direction is demotion: the parameter is higher-kinded for a use that
   erasure has made vacuous.  Note this is narrower than "demote higher-kinded
   parameters" -- the Vellvm artifact has 19 of them and the 15 outside the
   event path receive genuine class templates (`tfmap<List::list>`).  The rule
   has to be about what is being abstracted over, not about kinds in general.
   See the `hkt-kind-demotion-dead-end` note. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Monads.ITreeReified.
From ITree Require Import ITree.
Require Import List.

Inductive void : Set := .

(* Index, not parameter, and two constructors: emits a plain struct. *)
Inductive UBE : Type -> Type :=
| throwub : unit -> UBE void
| ubread  : unit -> UBE nat.

(* ITreeUtil.trigger_cast', verbatim: the family parameter is applied in the
   domain and named in the codomain, and the codomain drops it. *)
Definition void_elim {A} : void -> A := fun v => match v with end.

Definition trigger_cast' {E : Type -> Type} {A : Type} (e : E void)
  : itree E A := ITree.bind (ITree.trigger e) (fun x => void_elim x).

Module SkippedDictFamilyUnconstrained.
  (* LLVMEvents.raiseUB: the only occurrence of [E] is the subevent class,
     and that class is skipped. *)
  Definition raiseUB {E} `{UBE -< E} {X} : itree E X :=
    trigger_cast' (subevent _ (throwub tt)).

  Definition run : itree UBE nat := raiseUB.
End SkippedDictFamilyUnconstrained.

Crane Extraction "skipped_dict_family_unconstrained"
  SkippedDictFamilyUnconstrained.
