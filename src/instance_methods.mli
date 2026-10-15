(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A type-class instance's methods as Core elaborates them
    (docs/Pipeline-Disentangling-Plan.md, section 4.7: [ElaborateInstances]).

    An instance is a record of its class built under the instance's own
    parameters.  Each method is generated from its field of that record, but
    not as written: the field's type gets back the method's own quantifier,
    the instance's class arguments are substituted into it, the body's type
    variables are renumbered to match, and a body extraction eta-reduced below
    the field's declared arity is expanded back to it.  This module is all of
    that, in Core terms alone, so that the elaborated bodies are a value both
    the walk elaborating a unit's calls ({!Core_elaborate}) and the generator
    of the instance's struct ({!Gen_instances}) read, rather than something
    the generator works out while it emits. *)

(** An instance's type and body past its own parameters: erased type binders
    and class dictionaries, an eta-reduced instance's included.  [lam_params]
    is every binder stripped, outermost first; [dictionaries] the
    class-typed ones, each named the way the instance's template parameter for
    it is ({!Common.tc_instance_id}), with the class the instance's type
    states. *)
type layers = {
  inner_ty : Miniml.ml_type;
  inner_body : Miniml.ml_ast;
  dictionaries : (Names.Id.t * Miniml.ml_type) list;
  lam_params : (Names.Id.t * Miniml.ml_type) list;
}

val layers : Miniml.ml_type -> Miniml.ml_ast -> layers

(** [record_body name class_ref inner_ty lam_params inner_body] -- the record
    the instance [name] builds.  A singleton class's instance is its method:
    past the instance's own parameters, the body is the record's one field.
    A fixpoint is the method calling itself, through this very instance. *)
val record_body :
  Names.GlobRef.t ->
  Names.GlobRef.t ->
  Miniml.ml_type ->
  (Names.Id.t * Miniml.ml_type) list ->
  Miniml.ml_ast ->
  Miniml.ml_ast

(** The class arguments of an instance whose record constructor is typed
    [cons_ty] and whose declared type gives [type_args]: the constructor's
    where it says more, the declaration's where the constructor erased one. *)
val record_type_args : Miniml.ml_type -> Miniml.ml_type list -> Miniml.ml_type list

(** [class_type ty] -- the class type of an instance of type [ty]: past its
    own parameters, erased type binders and class dictionaries; the
    [inner_ty] {!layers} reaches. *)
val class_type : Miniml.ml_type -> Miniml.ml_type

(** [instance_tvars ty inner_ty] -- the type variables the instance of type
    [ty], whose class type past its parameters is [inner_ty], declares a
    template parameter for, in ascending order: those its class arguments
    and its dictionaries' constraints mention, less the carriers a dictionary
    is about. *)
val instance_tvars : Miniml.ml_type -> Miniml.ml_type -> int list

(** [tvar_count ~instance_tvars ty type_args] -- how many type variables the
    instance binds: not the number of template parameters it declares, but
    every variable its type or its class arguments name. *)
val tvar_count : instance_tvars:int list -> Miniml.ml_type -> Miniml.ml_type list -> int

(** An instance as its methods are elaborated against: its class, the class
    arguments it gives ({!record_type_args}), and how many type variables it
    binds ({!tvar_count}). *)
type instance = {
  class_ref : Names.GlobRef.t;
  type_args : Miniml.ml_type list;
  tvar_count : int;
}

(** [subst_promoted_tvars inst ty] -- [ty] with each of the class's promoted
    variables the instance gives a type, a variable past the ones it binds,
    replaced by that type. *)
val subst_promoted_tvars : instance -> Miniml.ml_type -> Miniml.ml_type

(** One method of an instance, elaborated. *)
type method_ = {
  field_ml_ty : Miniml.ml_type;
      (** The field's type with the method's own quantifier recovered, its
          variables numbered past every variable of the instance. *)
  subst_args : Miniml.ml_type list;
      (** The class arguments substituted into it, a higher-kinded carrier's
          eta-expanded arguments taken off. *)
  subst_ty : Miniml.ml_type;  (** {!field_ml_ty} at {!subst_args}. *)
  n_method_tvars : int;  (** How many variables the method quantifies itself. *)
  declared_arity : int;  (** How many value arrows the class declared it at. *)
  body : Miniml.ml_ast;
      (** The body, at the declared types and expanded to the declared
          arity. *)
}

(** [args_and_ret m] -- {!method_.subst_ty} split at the declared arity: its
    parameters, erased and class-typed ones included, and the rest as the
    result. *)
val args_and_ret : method_ -> Miniml.ml_type list * Miniml.ml_type

(** {!args_and_ret} of {!method_.field_ml_ty}, the class's own statement. *)
val declared_args_and_ret : method_ -> Miniml.ml_type list * Miniml.ml_type

(** [prepare_method inst method_ref field_ml_ty field_body] -- the method
    [method_ref] of [inst], declared by the class at [field_ml_ty], whose field
    the instance's record fills with [field_body].  With [freshen] (the
    default) the body's open annotations are given identities of their own,
    which each generation of the method needs. *)
val prepare_method :
  ?freshen:bool -> instance -> Names.GlobRef.t -> Miniml.ml_type -> Miniml.ml_ast -> method_

(** One of the leading binders of a method's body, as its accessor takes it:
    a parameter, or [erased] -- no parameter, but still a binder the body
    counts through. *)
type param = {
  binder : Miniml.ml_ident;
  binder_ty : Miniml.ml_type;
  erased : bool;
}

(** [params m] -- the binders {!method_.body} opens with that the accessor
    takes, up to the declared arity, and the body past them. *)
val params : method_ -> param list * Miniml.ml_ast

(** [eta_call m inner_body] -- for a method whose accessor takes no parameter
    from its body ({!params}), the parameters it is eta-expanded with, named
    [a0], [a1], ..., one per declared argument that is neither erased nor
    class-typed, and [inner_body] applied to them; [None] where there is no
    such argument, the field being a value. *)
val eta_call : method_ -> Miniml.ml_ast -> ((Names.Id.t * Miniml.ml_type) list * Miniml.ml_ast) option

(** [methods name body ty] -- the methods the instance [name], [body] of type
    [ty], generates, each elaborated ({!prepare_method}, its open annotations
    left as they are), with the binders of the instance's own parameters
    ({!layers}) they are generated under; [None] for a declaration building no
    record of a class. *)
val methods :
  Names.GlobRef.t -> Miniml.ml_ast -> Miniml.ml_type -> ((Names.Id.t * Miniml.ml_type) list * method_ list) option
