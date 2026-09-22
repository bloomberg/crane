(* A carrier that resists being named is written as a name in a *type*
   position, where naming it is ill-formed.

   A class carrier that is a lambda over a two-parameter constructor --
   [fun T => two T (FnBody T)] -- has no namespace-scope alias to be: its body
   names [FnBody], a template parameter of the enclosing declaration.  The
   printer mints a holder for it,

     template <template <typename> class _F0> struct _crane_carrier_tch {
       template <typename _CraneTcArg> using c = two<_CraneTcArg, _F0<_CraneTcArg>>;
     };

   and writes the carrier as [_crane_carrier_tch<T1>::template c].  At a
   template template argument that is exactly right, and
   [hk_constraint_carrier_two_params] already checks it.

   Here the same carrier reaches a *type* position.  [m_items] is a [list] of
   it, so the dictionary the inner [tfmap] wants is eta-expanded into a lambda,
   and the lambda's parameter and result are spelled from the callee's
   declaration with the carrier substituted in:

     [](std::function<std::any(std::any)> _x0,
        List<_crane_carrier_tch<T1>::template c<std::any>> _x1)
        -> List<_crane_carrier_tch<T1>::template c<std::any>> { ... }

   which is ill-formed.  A typename-specifier may not name an alias template
   member ([temp.res]); clang reports it as

     error: typename specifier refers to alias template member in
            '_crane_carrier_tch<cfg>'; argument deduction not allowed here

   -- wording that names a syntactic rule rather than describing a deduction,
   since the enclosing template is already substituted by then.

   The two occurrences are not one defect.  A template template argument needs
   the abstraction's *name*, and there the holder member is the only spelling
   there is.  A type position needs the abstraction *applied*, and an applied
   abstraction is just its body with the argument substituted --
   [two<std::any, T1<std::any>>] -- which is the same type and a plain one.
   So the fix is not to make the ill-formed construct legal but to stop
   writing it: reduce the application where the abstraction lands in head
   position.

   Making it legal is in fact unavailable.  Emitting [c] as a nested class
   template rather than a [using] would satisfy the rule and change the type:
   the field really holds a [two<...>], and a struct wrapping one is a fresh
   type that no longer matches.  Transparency is what the alias is for.

   What it takes to reach this, which is narrower than it looks.  Three things
   have to hold at once, and dropping any one of them produces C++ that
   compiles:

   - the carrier must be a composite that {e resists naming}: [T] occurring
     twice, once bare and once under the higher-kinded variable.  Where the
     carrier is the bare variable, as in [hk_constraint_carrier_two_params],
     there is a name already and no holder is minted;
   - the demand must come from {e inside} an instance whose own head is also a
     composite, so that the dictionary is eta-expanded rather than named;
   - the eta-expansion must be at a site with written parameter types.  A
     carrier in which [T] occurs only under the higher-kinded variable
     ([fun T => list (G T)]) gives the lambda [auto &&] parameters instead,
     and the spelling never has to be chosen.

   Vellvm: rocq/Syntax/Traversal.v:859, [TFunctor_modul], whose head is the
   composite [fun T => modul (FnBody T)] and whose body demands a dictionary
   for the second, doubled composite [fun T => definition T (FnBody T)] --
   [m_definitions : list (definition T FnBody)], CFG.v:66.  The control is
   [TFunctor_definition] at the same higher-kindedness, whose carrier is the
   bare variable and which writes [definition<std::any, T1<std::any>>]
   applied, and compiles. *)

From Crane Require Import Mapping.Std.
From Stdlib Require Import List.

Class TFunctor (T : Set -> Set) := tfmap : forall {U V : Set} (f : U -> V), T U -> T V.

#[global] Instance TFunctor_list : TFunctor list | 50 := List.map.

(* The composite [fun T => list (G T)].  [T] occurs once, under [G], so this
   carrier has a name and is not itself the defect -- it is what puts the
   doubled carrier below into a type position. *)
#[global] Instance TFunctor_list_of {G : Set -> Set} `{TFunctor G}
  : TFunctor (fun T => list (G T)) | 60 :=
  fun U V f l => List.map (tfmap f) l.

(* Two parameters, as Vellvm's [definition T FnBody] has. *)
Record two (T : Set) (Body : Set) : Set := mk_two { t_head : T ; t_body : Body }.

(* The carrier that resists naming: [T] bare in one argument and under
   [FnBody] in the other. *)
#[global] Instance TFunctor_two {FnBody : Set -> Set} `{TFunctor FnBody}
  : TFunctor (fun T => two T (FnBody T)) | 50 :=
  fun U V f p => mk_two _ _ (f (t_head _ _ p)) (tfmap f (t_body _ _ p)).

Record modul (T : Set) (Body : Set) : Set :=
  mk_modul { m_items : list (two T Body) }.

(* The instance head is itself a composite, and its body demands a dictionary
   for a second, different one.  That nesting is what forces the eta-expansion
   at a site where the parameter types are written out. *)
#[global] Instance TFunctor_modul {FnBody : Set -> Set}
       `{TFunctor FnBody}
       `{TFunctor (fun T => two T (FnBody T))}
  : TFunctor (fun T => modul T (FnBody T)) | 50 :=
  fun U V f m => mk_modul _ _ (tfmap f (m_items _ _ m)).

Module HkCarrierAliasAppliedAsType.

  Definition run (m : modul nat (list nat)) : modul nat (list nat) :=
    tfmap S m.

End HkCarrierAliasAppliedAsType.

Crane Extraction "hk_carrier_alias_applied_as_type" HkCarrierAliasAppliedAsType.
