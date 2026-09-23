(* An instance method's body erases an associated type its own declaration
   resolved.

     template <IPtr _tcI0> struct PointerV {
       using iptr = typename _tcI0::iptr;
       using ptr = std::pair<iptr, prov>;
       static std::pair<iptr, prov> null() {
         return std::make_pair(std::any(_tcI0::zero_iptr()), nil_prov);
       }
     };

   The signature resolves [iptr] through the instance parameter; the body
   wraps the same value in [std::any], which is how the {e class} declares the
   field ([using iptr = std::any] at the concept).  The two disagree within
   one struct, so the error is a conversion and not an arity.

   This is the [ParamsV] disagreement one level down: there the declaration
   consulted erasure and the use site did not, in a template argument list;
   here the declaration consults the instance and the body does not, in an
   expression.

   Vellvm: [vellvm_bench.h:12326], [PointerV::null], and the same split at
   [:80473] -- [const ptr] against [std::pair<Z, ...>], [const iptr] against
   [Z], and [std::function<bool (Z, Z)>] against
   [std::function<bool (std::any, std::any)>].  The dominant family of the 41
   unique errors the [ParamsV] fix unmasked: that arity failure kept
   [ParamsV<IPZ>] from instantiating, so nothing inside it had ever been
   checked. *)

From Crane Require Import Mapping.Std.
From Stdlib Require Import List.

Class IPtr := { iptr : Set ; zero_iptr : iptr }.

#[global] Instance IPZ : IPtr := { iptr := nat ; zero_iptr := 0 }.

Definition prov : Set := list nat.
Definition nil_prov : prov := nil.

Class PTR := { ptr : Set ; null : ptr }.

#[global] Instance PointerV {IP : IPtr} : PTR :=
  { ptr := (iptr * prov)%type ; null := (zero_iptr, nil_prov) }.

Module AssocTypeErasedInBody.
  Definition go (_ : nat) : nat := fst (@null (@PointerV IPZ)).
End AssocTypeErasedInBody.

Crane Extraction "assoc_type_erased_in_body" AssocTypeErasedInBody.
