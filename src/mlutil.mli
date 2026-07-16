(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Utility functions over ML types and terms, type environments, and
    optimization passes. *)

open Names
open Miniml
open Table

(** {2 Utility functions over ML types with meta} *)

(** Reset the meta variable counter. *)
val reset_meta_count : unit -> unit

(** Create a fresh meta variable. *)
val new_meta : 'a -> ml_type

(** Substitute type variables using a list of types.
    @param l replacement types for [Tvar 1], [Tvar 2], ... in order
    @param t the ML type to substitute into *)
val type_subst_list : ml_type list -> ml_type -> ml_type

(** Substitute type variables using an array of types.
    @param v replacement types for [Tvar 1], [Tvar 2], ... (zero-indexed in the array)
    @param t the ML type to substitute into *)
val type_subst_vect : ml_type array -> ml_type -> ml_type

(** Instantiate a type schema with fresh meta variables. *)
val instantiation : ml_schema -> ml_type

(** Replace unknown meta variables with fresh type variables. *)
val instantiate_unknowns : ml_type -> ml_type

(** Attempt most general unification of two types.  Mutably updates
    metavariable bindings on success; silently does nothing on failure.
    @param t1 first type
    @param t2 second type *)
val try_mgu : ml_type -> ml_type -> unit

(** Determine if a type coercion requires magic (unsafe cast).
    @param p a pair [(expected, actual)] of ML types to compare
    @return [true] if the types cannot be unified and [MLmagic] is needed *)
val needs_magic : ml_type * ml_type -> bool

(** Conditionally wrap an ML term with magic if the flag is true.
    @param b when [true], wraps [a] in [MLmagic]
    @param a the ML expression to (possibly) wrap *)
val put_magic_if : bool -> ml_ast -> ml_ast

(** Wrap an ML term with magic if the type pair requires it.
    @param p a pair [(expected, actual)] of ML types
    @param a the ML expression to (possibly) wrap *)
val put_magic : ml_type * ml_type -> ml_ast -> ml_ast

(** Check if an ML term can be generalized. *)
val generalizable : ml_ast -> bool

(** {2 ML type environment} *)

module Mlenv : sig
  type t

  (** The empty type environment. *)
  val empty : t

  (** Get the n-th most recently entered schema and instantiate it.
      @param mle the type environment
      @param n 1-based index into the environment (1 = most recently pushed)
      @return a fresh instantiation of the n-th schema *)
  val get : t -> int -> ml_type

  (** Add a type to the environment, after generalizing free meta variables.
      @param mle the current environment
      @param t  the ML type to generalize and push *)
  val push_gen : t -> ml_type -> t

  (** Add a type with no [Tvar] (no generalization needed).
      @param mle the current environment
      @param t  the monomorphic ML type to push *)
  val push_type : t -> ml_type -> t

  (** Add a type with no [Tvar] nor [Tmeta] (no generalization, no free metas).
      @param mle the current environment
      @param t  the ground ML type to push *)
  val push_std_type : t -> ml_type -> t
end

(** {2 Utility functions over ML types without meta} *)

(** Check if a mutual inductive name occurs in a type.
    @param kn the mutual inductive kernel name to search for
    @param t  the ML type to search in
    @return [true] if [kn] appears inside a [Tglob] node of [t] *)
val type_mem_kn : MutInd.t -> ml_type -> bool

(** Return the maximum type variable index in a type.
    @return the largest [i] such that [Tvar i] or [Tvar' i] occurs in [t],
            or [0] if no type variable is present *)
val type_maxvar : ml_type -> int

(** Decompose an ML type into a list of argument types and a result type.
    @return [(args, result)] where [args] are the curried parameter types
            and [result] is the final return type *)
val type_decomp : ml_type -> ml_type list * ml_type

(** Recompose an ML type from a list of argument types and a result type.
    @param args the list of argument types (left-to-right)
    @param result the final return type *)
val type_recomp : ml_type list * ml_type -> ml_type

(** Convert type variables to primed type variables. *)
val var2var' : ml_type -> ml_type

(** Abbreviation map type for looking up type aliases. *)
type abbrev_map = GlobRef.t -> ml_type option

(** Expand type abbreviations using the given map.
    @param env lookup function mapping global references to their type bodies;
               return [None] to leave a [Tglob] unexpanded
    @param t   the ML type to expand *)
val type_expand : abbrev_map -> ml_type -> ml_type

(** Simplify an ML type. *)
val type_simpl : ml_type -> ml_type

(** Convert an ML type to a signature element for its outermost position.
    @param env abbreviation map for expanding type aliases
    @param t   the ML type to classify
    @return [Kill d] if the outermost type is [Tdummy d] (and not conservative),
            [Keep] otherwise *)
val type_to_sign : abbrev_map -> ml_type -> sign

(** Convert an ML type to a full argument signature by decomposing arrows.
    @param env abbreviation map for expanding type aliases
    @param t   the ML type to decompose
    @return a [signature] with one entry per curried argument position *)
val type_to_signature : abbrev_map -> ml_type -> signature

(** Expunge dummy arguments from an ML type using the abbreviation map.
    @param env abbreviation map for expanding type aliases
    @param t   the ML type from which to remove [Tdummy] arrows *)
val type_expunge : abbrev_map -> ml_type -> ml_type

(** Expunge dummy arguments from an ML type guided by a pre-computed signature.
    @param env abbreviation map for expanding type aliases
    @param s   the signature indicating which arguments are [Kill]ed
    @param t   the ML type from which to remove the killed arrow positions *)
val type_expunge_from_sign : abbrev_map -> signature -> ml_type -> ml_type

(** Test equality of two ML types. *)
val eq_ml_type : ml_type -> ml_type -> bool

(** Check if a type is Tdummy. *)
val isTdummy : ml_type -> bool

(** Check if an ML term is MLdummy. *)
val isMLdummy : ml_ast -> bool

(** Check if a sign is Kill. *)
val isKill : sign -> bool

(** Expunge dummy arguments from a case expression, eta-expanding as needed.
    @param s the signature indicating which leading arguments are [Kill]ed
    @param e the ML expression (typically a match branch body) to process
    @return [(ids, body)] with the surviving binders and the stripped body *)
val case_expunge : signature -> ml_ast -> (ml_ident * ml_type) list * ml_ast

(** Expunge dummy leading lambdas from a term according to a signature.
    Leaves one dummy lambda when all arguments are logical and the target
    language is strict.
    @param s        the signature indicating which leading lambdas are [Kill]ed
    @param ids_body a pair [(binders, body)] as returned by [collect_lams]
    @return the term with killed lambdas removed *)
val term_expunge : signature -> (ml_ident * ml_type) list * ml_ast -> ml_ast

(** {2 Special identifiers}

    [dummy_name] is to be used for dead code and will be printed as [_] in
    concrete (Caml) code. *)

(** The anonymous identifier used for unnamed binders. *)
val anonymous_name : Id.t

(** The dummy identifier used for dead code. *)
val dummy_name : Id.t

(** Convert a Name.t to an Id.t, using anonymous_name for anonymous names. *)
val id_of_name : Name.t -> Id.t

(** Extract the Id.t from an ml_ident. *)
val id_of_mlid : ml_ident -> Id.t

(** Generate a temporary identifier from an ml_ident. *)
val tmp_id : ml_ident -> ml_ident

(** {2 Lambda collection}

    [collect_lams MLlam(id1,...MLlam(idn,t)...)] returns the list [idn;...;id1]
    and the term [t]. *)

(** Collect all lambda abstractions from a term. *)
val collect_lams : ml_ast -> (ml_ident * ml_type) list * ml_ast

(** Collect exactly n lambda abstractions from a term.
    @param n the number of leading [MLlam] nodes to collect; asserts if fewer exist
    @param t the term to peel
    @return [(binders, body)] where [binders] has exactly [n] entries (outermost first) *)
val collect_n_lams : int -> ml_ast -> (ml_ident * ml_type) list * ml_ast

(** Remove n lambda abstractions from a term.
    @param n the number of leading [MLlam] nodes to drop; asserts if fewer exist *)
val remove_n_lams : int -> ml_ast -> ml_ast

(** Count the number of lambda abstractions at the head of a term. *)
val nb_lams : ml_ast -> int

(** Wrap a term in lambda abstractions with the given identifiers and types.
    @param ids list of [(identifier, type)] pairs, outermost binder first
    @param a   the body to wrap *)
val named_lams : (ml_ident * ml_type) list -> ml_ast -> ml_ast

(** Wrap a term in n dummy lambda abstractions.
    @param a the body to wrap
    @param n the number of [MLlam(Dummy,...)] layers to add *)
val dummy_lams : ml_ast -> int -> ml_ast

(** Wrap a term in anonymous or dummy lambda abstractions based on the
    signature.
    @param a the body to wrap
    @param s the signature; [Keep] entries become anonymous lambdas, [Kill k]
             entries become [Dummy] lambdas with [Tdummy k] type *)
val anonym_or_dummy_lams : ml_ast -> signature -> ml_ast

(** Wrap a term in anonymous or dummy lambda abstractions with concrete types.
    Like [anonym_or_dummy_lams] but uses actual resolved ML types for [Keep]
    positions instead of [Taxiom].
    @param a     the body to wrap
    @param types ML types for the [Keep] positions, matched positionally;
                 falls back to [Taxiom] when the list runs out
    @param s     the signature driving the lambda structure *)
val anonym_or_dummy_lams_typed : ml_ast -> ml_type list -> signature -> ml_ast

(** Generate eta-expanded argument list based on arity and signature.
    @param n the starting de Bruijn level (counts down)
    @param s the signature; [Keep] entries emit [MLrel] arguments,
             [Kill] entries are skipped
    @return the list of [MLrel] arguments for the kept positions *)
val eta_args_sign : int -> signature -> ml_ast list

(** {2 Utility functions over ML terms} *)

(** Apply an ML term to a list of arguments. Returns [f] unchanged when [a] is empty. *)
val mlapp : ml_ast -> ml_ast list -> ml_ast

(** Map a function over all immediate subterms.
    @param f the transformation to apply to each direct child
    @param t the ML AST node whose children are to be mapped *)
val ast_map : (ml_ast -> ml_ast) -> ml_ast -> ml_ast

(** Map a function over all immediate subterms with a binding-depth counter.
    @param f   the transformation; receives the current depth and the child term
    @param n   the current binding depth (passed to [f] for each child)
    @param t   the ML AST node whose children are to be mapped *)
val ast_map_lift : (int -> ml_ast -> ml_ast) -> int -> ml_ast -> ml_ast

(** Iterate a function over all immediate subterms.
    @param f the action to perform on each direct child
    @param t the ML AST node to iterate over *)
val ast_iter : (ml_ast -> unit) -> ml_ast -> unit

(** Check if a de Bruijn index occurs in a term.
    @param k the de Bruijn index to look for (1-based, relative to [t])
    @param t the term to search
    @return [true] if [MLrel k] appears free in [t] *)
val ast_occurs : int -> ml_ast -> bool

(** Check if any de Bruijn index in the interval [[k, k']] occurs in a term.
    @param k  lower bound of the index range (inclusive)
    @param k' upper bound of the index range (inclusive)
    @param t  the term to search
    @return [true] if some [MLrel i] with [k <= i <= k'] appears free in [t] *)
val ast_occurs_itvl : int -> int -> ml_ast -> bool

(** Lift de Bruijn indices in a term.
    @param k the amount to add to each free de Bruijn index in [t]
    @param t the term whose free indices are to be lifted *)
val ast_lift : int -> ml_ast -> ml_ast

(** Pop the outermost de Bruijn level (equivalent to [ast_lift (-1)]). *)
val ast_pop : ml_ast -> ml_ast

(** Substitute a term for de Bruijn index 1, adjusting other indices.
    @param e the term to substitute for [Rel 1]
    @param t the term in which the substitution is performed *)
val ast_subst : ml_ast -> ml_ast -> ml_ast

(** Substitute global references in a term using the given map.
    @param s a map from [GlobRef.t] to replacement [ml_ast] bodies
    @param t the term in which to perform the substitution *)
val ast_glob_subst : ml_ast Refmap'.t -> ml_ast -> ml_ast

(** Remove unused variable bindings from a term. *)
val dump_unused_vars : ml_ast -> ml_ast

(** Normalize an ML term by beta-reduction and simplification. *)
val normalize : ml_ast -> ml_ast

(** Optimize fixpoint expressions. *)
val optimize_fix : ml_ast -> ml_ast

(** Determine if a global reference should be inlined in the given term.
    @param r the global reference of the constant to test
    @param t the current extracted body of [r]
    @return [true] if [r] should be inlined at call sites *)
val inline : GlobRef.t -> ml_ast -> bool

(** Check if a pattern is a basic (non-nested) pattern. *)
val is_basic_pattern : ml_pattern -> bool

(** Check if any branch has a deep (nested) pattern. *)
val has_deep_pattern : ml_branch array -> bool

(** Check if a match is regular (all patterns are basic). *)
val is_regular_match : ml_branch array -> bool

(** Exception raised when an operation is impossible. *)
exception Impossible

(** {2 Classification of signatures} *)

(** Classification of signatures based on their contents. *)
type sign_kind =
  | EmptySig
  | NonLogicalSig (* at least a [Keep] *)
  | SafeLogicalSig (* only [Kill Ktype] *)
  | UnsafeLogicalSig (* No [Keep], not all [Kill Ktype] *)

(** Classify a signature into one of the sign_kind categories.
    @return [EmptySig] for an empty list; [NonLogicalSig] if any [Keep] is
            present; [SafeLogicalSig] if all entries are [Kill Ktype];
            [UnsafeLogicalSig] otherwise *)
val sign_kind : signature -> sign_kind

(** Remove trailing Keep elements from a signature. *)
val sign_no_final_keeps : signature -> signature

(** Remap type variable indices in a term using the given function.
    @param f   a function from old type variable index to new index; applied to
               every [Tvar] and [Tvar'] annotation occurring in the term
    @param t   the ML AST in which to remap type variable indices *)
val remap_tvars : (int -> int) -> ml_ast -> ml_ast
