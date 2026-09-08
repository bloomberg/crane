(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** This module collects the predicates and transformations over MiniML types
   ([Miniml.ml_type]) and C++ types ([Minicpp.cpp_type]) that are used
   throughout the Coq -> C++ extraction pipeline. It provides type
   classification (erased / unit / void / list / option / prod / monadic /
   value types), arrow and codomain analysis, type-variable substitution and
   erasure, and constructor-name resolution. It also exposes a block of
   well-known Coq constructor indices (positive, Z, decimal, hex, signed,
   etc.) so that numeric-literal encodings can be recognised by tag. *)

(** {2 Asking whether a type is erased}

    Several predicates here answer some version of "is this [std::any]", and
    picking the wrong one silently yields [false] rather than an error.  They
    sit at three layers, and the layer is the thing to choose by:

    - {b Structural} (this module): {!prints_as_any}, {!is_boxed_type},
      {!is_cpp_dummy_type}, {!has_tany_in_type}, {!has_erased_type_in_type}.
      These look only at the type node in front of them.  They cannot see
      through a [using] alias, so a caller holding a type that {e might} be
      an alias must run [Translation.unfold_cpp_typedef] first.  Note also
      that a [Tdummy] converts to a [dummy_type] marker, not to [Tany]:
      {!has_tany_in_type} misses it and {!has_erased_type_in_type} does not.
    - {b Environment-aware} ([translation.ml]): [resolves_to_any_type],
      [spells_as_any], [is_boxed_source], and above all [classify_erasure],
      which is the one to reach for when the question is whether a {e value}
      may be boxed or cast.  These follow the ML type table and the typedef
      chain.
    - {b Printer} ([cpp_erasure.ml]): [is_any_shaped], which consults the
      alias set accumulated while emitting declarations, and so is only
      meaningful during printing. *)

(** {2 Constructor name resolution} *)

(** Struct name for the C++ representation of a constructor global reference. *)
val ctor_struct_name_of_ref : ?fallback_idx:int -> Names.GlobRef.t -> string

(** Struct identifier for the C++ representation of a constructor global reference. *)
val ctor_struct_id_of_ref :
  ?fallback_idx:int -> Names.GlobRef.t -> Names.variable

(** {2 Type resolution and variable maps} *)

(** Resolve a MiniML type through any metavariable indirection. *)
val resolve_tmeta : Miniml.ml_type -> Miniml.ml_type

(** Unfold a type alias whose body is a function type, substituting the
    alias's own type arguments; any other type is returned unchanged. *)
val expand_ml_fun_alias : Miniml.ml_type -> Miniml.ml_type

(** Build the substitution mapping type variables of one C++ type to the
    corresponding sub-types of another. *)
val extract_tvar_map :
  Minicpp.cpp_type ->
  Minicpp.cpp_type -> (Names.variable * Minicpp.cpp_type) list

(** Find the arguments of a self- or mutually-recursive occurrence in a type. *)
val find_self_ref_args :
  is_self_or_mutual:(Names.GlobRef.t -> bool) ->
  Miniml.ml_type -> Miniml.ml_type list option

(** {2 Erasure classification} *)

(** Whether a MiniML type is fully erased. *)
val is_erased_ml_type : Miniml.ml_type -> bool

(** Whether a MiniML type contains an erased component anywhere within it. *)
val ml_type_contains_erased : Miniml.ml_type -> bool

(** {2 Arrow and codomain analysis} *)

(** The codomain (final result type) of a MiniML arrow type. *)
val ml_codomain : Miniml.ml_type -> Miniml.ml_type

(** [ml_drop_arrows n t] is what is left of [t] once [n] of its value-carrying
    arrows have been applied; [Tunresolved] if it has fewer than [n]. *)
val ml_drop_arrows : int -> Miniml.ml_type -> Miniml.ml_type

(** Count the number of value-carrying arrows in a MiniML type. *)
val count_ml_value_arrows : Miniml.ml_type -> int

(** Whether the codomain of a MiniML type is a type variable. *)
val ml_codomain_is_tvar : Miniml.ml_type -> bool

(** Count the total number of arrows in a MiniML type. *)
val count_ml_arrows : Miniml.ml_type -> int

(** Whether a MiniML type is monadic. *)
val is_monadic_ml_type : Miniml.ml_type -> bool

(** {2 Unit and void classification} *)

(** Whether a MiniML type is void. *)
val ml_type_is_void : Miniml.ml_type -> bool

(** Whether a MiniML type is unit. *)
val ml_type_is_unit : Miniml.ml_type -> bool

(** Whether a C++ type is the unit type. *)
val is_cpp_unit_type : Minicpp.cpp_type -> bool

(** Rewrite occurrences of the unit type into void within a C++ type. *)
val voidify_unit_in_type : Minicpp.cpp_type -> Minicpp.cpp_type

(** Whether a MiniML type is unit or void. *)
val ml_type_is_unit_or_void : Miniml.ml_type -> bool

(** {2 Value-type filtering} *)

(** Keep only the value-carrying types from a list of MiniML types. *)
val filter_value_types : Miniml.ml_type list -> Miniml.ml_type list

(** Whether the codomain of a MiniML type erases to [any]. *)
val ml_codomain_erases_to_any :
  ?has_dummy:bool -> int -> Miniml.ml_type -> bool

(** {2 Type variables in C++ types} *)

(** Whether a C++ type contains a type variable. *)
val contains_tvar : Minicpp.cpp_type -> bool

(** Whether a C++ type contains a type variable not bound by the given list. *)
val has_unbound_tvar : Names.variable list -> Minicpp.cpp_type -> bool

(** {2 Well-known global references} *)

(** Whether a global reference is [option]. *)
val is_option_global : Names.GlobRef.t -> bool

(** Whether a global reference is [prod]. *)
val is_prod_global : Names.GlobRef.t -> bool

(** Structural equality of two C++ types. *)
val cpp_ty_eq : Minicpp.cpp_type -> Minicpp.cpp_type -> bool

(** Whether a global reference is [list]. *)
val is_list_global : Names.GlobRef.t -> bool

(** Struct names for the two [list] constructors (cons and nil). *)
val list_ctor_struct_names : Names.GlobRef.t -> string * string

(** {2 Dummy and erased C++ types} *)

(** Whether a C++ type is the dummy type. *)
val is_cpp_dummy_type : Minicpp.cpp_type -> bool

(** The type under any module or namespace qualification.  Questions about
    what a type {i is} -- which inductive, at which instantiation -- are about
    the type inside the qualification, not the wrapper. *)
val unqualify_ty : Minicpp.cpp_type -> Minicpp.cpp_type

(** Whether a C++ type is spelled [std::any] in the generated header.  A
    question about syntax only — it says nothing about whether a value of the
    type may be boxed or cast, for which see {!is_boxed_type}. *)
val prints_as_any : Minicpp.cpp_type -> bool

(** True of a function type whose whole signature erased to [std::any]. *)
val is_fully_erased_fun_ty : Minicpp.cpp_type -> bool

(** True of a function type that erased its arguments but kept a concrete
    result, so a closure reaching it needs the [crane_erase_fn] adapter. *)
val partially_erased_fun_ty : Minicpp.cpp_type -> bool

(** Whether a value of this type is known to live inside a [std::any], and so
    may be boxed into and [any_cast] out of.  Narrower than {!prints_as_any}:
    {!Minicpp.Topaque} prints as [std::any] but claims nothing about the
    representation, and is excluded. *)
val is_boxed_type : Minicpp.cpp_type -> bool


(** Replace every {!Minicpp.Topaque} in a type with {!Minicpp.Tany}.  Apply at
    any position where the type is written down (field, parameter, return type,
    template argument): spelling [std::any] in a declaration is what makes the
    value boxed, so no [Topaque] may survive into the generated header. *)
val materialise_opaque : Minicpp.cpp_type -> Minicpp.cpp_type

(** Whether every component of a C++ type is erased. *)
val is_all_erased : Minicpp.cpp_type -> bool

(** The template arguments of a C++ type. *)
val extract_template_args : Minicpp.cpp_type -> Minicpp.cpp_type list

(** Erase a C++ type to [any]. *)
val erase_type_to_any : Minicpp.cpp_type -> Minicpp.cpp_type

(** [resolve_tvars_to_any ty] replaces every unresolved type variable in [ty]
    with [Tany], so an [any_cast] target has a C++ spelling. *)
val resolve_tvars_to_any : Minicpp.cpp_type -> Minicpp.cpp_type

(** Whether a MiniML type is an erased type. *)
val is_ml_erased_ty : Miniml.ml_type -> bool

(** {2 Skipped types} *)

(** Whether a C++ type should be skipped during extraction. *)
val is_skipped_cpp_type : Minicpp.cpp_type -> bool

(** Whether a MiniML type should be skipped during extraction. *)
val is_skipped_ml_type : Miniml.ml_type -> bool

(** {2 [any] and erasure detection} *)

(** Whether a C++ type contains [any] anywhere within it. *)
val has_tany_in_type : Minicpp.cpp_type -> bool

(** Whether a C++ type contains an erased type anywhere within it. *)
val has_erased_type_in_type : Minicpp.cpp_type -> bool

(** Whether a C++ type is a dummy Prop type. *)
val is_cpp_dummy_prop : Minicpp.cpp_type -> bool

(** Filter erased type arguments out of a C++ type-argument list, optionally
    preserving positions. *)
val filter_erased_type_args :
  ?preserve_positions:bool -> Minicpp.cpp_type list -> Minicpp.cpp_type list

(** {2 Type-variable presence, substitution, and erasure} *)

(** Whether a MiniML type contains a type variable. *)
val has_tvar : Miniml.ml_type -> bool

(** Map a transformation over all MiniML types embedded in an AST. *)
val map_types_in_ast :
  (Miniml.ml_type -> Miniml.ml_type) -> Miniml.ml_ast -> Miniml.ml_ast

(** Substitute type variables (by index) within a MiniML type. *)
val subst_tvars_type :
  (int * Miniml.ml_type) list -> Miniml.ml_type -> Miniml.ml_type

(** Erase type variables within a C++ type. *)
val tvar_erase_type : Minicpp.cpp_type -> Minicpp.cpp_type

(** Erase a type down to its outermost applied type constructors, boxing every
    leaf: [List<Nat>] becomes [List<std::any>], [Nat] becomes [std::any]. *)
val index_erase_type : Minicpp.cpp_type -> Minicpp.cpp_type

(** Whether a C++ type contains an unnamed type variable. *)
val has_unnamed_tvar : Minicpp.cpp_type -> bool

(** Whether a C++ type is erased. *)
val type_is_erased : Minicpp.cpp_type -> bool

(** {2 Function argument and return decomposition} *)

(** The final return type of a MiniML type. *)
val ml_return_type : Miniml.ml_type -> Miniml.ml_type

(** Split a MiniML type into its argument types and return type, given the
    already-known leading argument types. *)
val get_args_and_ret :
  Miniml.ml_type list ->
  Miniml.ml_type -> Miniml.ml_type list * Miniml.ml_type

(** Strip [n] leading arrows from a MiniML type, if possible. *)
val strip_tarr_n : int -> Miniml.ml_type -> Miniml.ml_type option

(** Strip reference and const qualifiers from a C++ type. *)
val strip_cpp_ref_const : Minicpp.cpp_type -> Minicpp.cpp_type

(** Count the real (non-erased) arguments among a list of MiniML AST nodes. *)
val count_real_ml_args : Miniml.ml_ast list -> int

(** {2 Value-type and copyability classification} *)

(** Whether a C++ type is an inductive value type. *)
val is_inductive_value_type : Minicpp.cpp_type -> bool

(** Whether a C++ type is trivially copyable. *)
val is_trivially_copyable_type : Minicpp.cpp_type -> bool

(** Whether a MiniML type is a non-trivial value type. *)
val is_nontrivial_value_ml_type : Miniml.ml_type -> bool

(** Whether a MiniML type is a product type. *)
val is_prod_ml_type : Miniml.ml_type -> bool


(** {2 Well-known Coq constructor tag indices} *)

(** Well-known Coq constructor tag indices (positive/Z/uint/decimal/hex/signed). *)
val positive_xI_idx : int

(** 1-based constructor index of [xO] (the [2n] case) in Rocq's
    [BinNums.positive]. *)
val positive_xO_idx : int

(** 1-based constructor index of [xH] (the [1] case) in Rocq's
    [BinNums.positive]. *)
val positive_xH_idx : int

(** 1-based constructor index of [Zpos] in Rocq's [BinNums.Z]
    (constructors [Z0], [Zpos], [Zneg]). *)
val z_pos_idx : int

(** 1-based constructor index of [Zneg] in Rocq's [BinNums.Z]. *)
val z_neg_idx : int

(** 1-based constructor index of [Nil] in Rocq's [Decimal.uint] and
    [Hexadecimal.uint]. *)
val uint_nil_idx : int

(** 1-based constructor index of [D0] in Rocq's [Decimal.uint]; the digit
    constructors [D0]..[D9] occupy the contiguous range
    [decimal_d0_idx]..[decimal_d9_idx]. *)
val decimal_d0_idx : int

(** 1-based constructor index of [D9], the last digit constructor of Rocq's
    [Decimal.uint]. *)
val decimal_d9_idx : int

(** 1-based constructor index of [D0] in Rocq's [Hexadecimal.uint]; the digit
    constructors [D0]..[Df] occupy the contiguous range
    [hex_d0_idx]..[hex_df_idx]. *)
val hex_d0_idx : int

(** 1-based constructor index of [Df], the last digit constructor of Rocq's
    [Hexadecimal.uint]. *)
val hex_df_idx : int

(** 1-based constructor index of [UIntDecimal] in Rocq's [Number.uint]. *)
val num_uint_decimal_idx : int

(** 1-based constructor index of [UIntHexadecimal] in Rocq's [Number.uint]. *)
val num_uint_hex_idx : int

(** 1-based constructor index of [Pos] in Rocq's [Decimal.signed_int] /
    [Hexadecimal.signed_int]. *)
val signed_pos_idx : int

(** 1-based constructor index of [Neg] in Rocq's [Decimal.signed_int] /
    [Hexadecimal.signed_int]. *)
val signed_neg_idx : int

(** {2 Template-parameter shape of a C++ signature} *)

(** Set of type-variable indices. *)
module IntSet : module type of Escape.IntSet

(** The 0-based [%tN] positions a custom template string mentions. *)
val template_referenced_positions : string -> IntSet.t

(** The type-argument positions a custom/monad global's template string
    mentions, or [None] when it has no template (all positions count). *)
val custom_referenced_positions_opt : Names.GlobRef.t -> IntSet.t option

(** [(index, name)] of every type variable in a C++ type, sorted by index. *)
val get_tvars_indexed : Minicpp.cpp_type -> (int * Names.Id.t) list

(** The names of the type variables in a C++ type, sorted by index. *)
val get_tvars : Minicpp.cpp_type -> Names.Id.t list

(** The indices of the type variables in a C++ type. *)
val get_tvar_indices : Minicpp.cpp_type -> int list

(** The type-variable indices a C++ type actually renders, skipping the
    positions a custom template drops. *)
val get_rendered_tvar_indices : Minicpp.cpp_type -> int list

(** [primary_tvar_indices dom cod] is the set of type-variable indices
    represented concretely in a generated signature, and so deducible from a
    call. The rest are phantom: a caller must spell them out. *)
val primary_tvar_indices :
  Minicpp.cpp_type list -> Minicpp.cpp_type -> IntSet.t

(** The type-variable indices appearing in type INDEX positions of inductives
    in an ML type. [convert_ml_type_to_cpp_type] strips these from the C++
    type, but function bodies may still need them for [any_cast]. *)
val collect_ml_type_index_tvars : Miniml.ml_type -> IntSet.t

(** Whether a function type returns a type variable its arguments carry only as
    an inductive's type index ([eval : expr A -> A]).  Such a result cannot be
    a template parameter -- the branches return genuinely different types -- so
    it is erased to [std::any] and recovered at the call. *)
val result_is_index_only_tvar : Miniml.ml_type -> bool

(** [explicit_tvar_prefix ~force_required cty] is how many leading template
    parameters of a signature of type [cty] a call must supply explicitly
    because the signature does not represent them. Only a leading run counts:
    C++ lets a call supply a prefix of the arguments and deduce the rest. *)
val explicit_tvar_prefix :
  ?force_required:IntSet.t -> Minicpp.cpp_type -> int
