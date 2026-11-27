(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The placeholder syntax of custom mappings ([Crane Extract Inductive],
    [Crane Extract Constant] and the like), parsed into tokens, once per text
    and category.  Literal C++ between placeholders stays opaque.  The only
    module that knows the syntax: translation and the printer
    ({!Cpp_passes.Erasure}) fold over the tokens. *)

(** One token of a parsed mapping. *)
type custom_case =
  | Scrut  (** [%scrut]: the scrutinee of a match template *)
  | Ty  (** [%ty]: the matched type *)
  | Body of int  (** [%br{i}]: branch [i]'s statements *)
  | Ty_arg of int  (** [%t{i}]: type argument [i] *)
  | Elem of int  (** [%elem{i}]: type argument [i], boxed where it recurses *)
  | Br_var of int * int  (** [%b{i}a{j}]: branch [i]'s binder [j] *)
  | Br_var_ty of int * int  (** [%b{i}t{j}]: the type of that binder *)
  | Text of string  (** literal text *)
  | Arg of int  (** [%a{i}]: value argument [i] *)
  | Ret  (** [%ret]: the type the call yields *)
  | Result  (** [%result]: the variable a block template assigns *)

(** The tokens of a type template: [%t{i}] and [%elem{i}] holes. *)
val type_template : string -> custom_case list

(** The tokens of a term template: a type template's holes, [%a{i}] and
    [%ret]. *)
val term_template : string -> custom_case list

(** The tokens of an inductive's match template. *)
val match_template : string -> custom_case list

(** One token of a [Drain "..."] template: literal statements, or a
    [%yield(e)] with its argument text. *)
type drain_token = Drain_text of string | Drain_yield of string

(** The tokens of a container's [Drain "..."] template. *)
val drain_template : string -> drain_token list

(** [Some i] when a term template is its value argument [i] and nothing
    else ([%a0]): the mapped term is that argument, in whatever position the
    term itself stands. *)
val passes_through : string -> int option

(** Whether a term template is a pair projection: [%a0.first] or
    [%a0.second]. *)
val is_pair_projection : string -> bool

(** The member of a pair the template [s] projects its one argument onto
    ([first] for ["%a0.first"]), when it is a pair projection. *)
val pair_projection_field : string -> string option

(** The binders [(i, j)] ([%b{i}a{j}]) the match template [s] writes outside
    any braces, and so declares in the scope the match is spliced into:
    [const auto& [%b0a0, %b0a1] = %scrut; %br0] declares both. *)
val unbraced_binders : string -> (int * int) list

(** How many times the template [s] splices its [i]-th value argument.  An
    argument past the last one it splices is applied to what it expands to,
    as a call's argument, and so is evaluated once -- every argument of a
    template that splices none, which is a callee. *)
val arg_mentions : string -> int -> int

(** Whether the template [s] splices each of its value arguments at most
    once, so that the C++ it expands to evaluates each exactly once. *)
val mentions_each_arg_once : string -> bool

(** The statements of a block template: a term template's holes and
    [%result], split at the semicolons of its own text that end a statement
    -- not one inside a string or character literal, or inside parentheses (a
    [for] header's).  A hole is never split: what is spliced into it is not
    read.  Each statement is trimmed of the blanks around it and has no
    semicolon of its own; a blank statement is dropped. *)
val block_statements : string -> custom_case list list

(** A mapping that names a template without saying where its arguments go
    takes them in order: ["Sum1"] at two arguments is ["Sum1<%t0, %t1>"]. *)
val custom_template_with_args : string -> int -> string

(** [type_arity tokens] is how many type arguments the template parsed into
    [tokens] names: one more than the highest [%t{i}] or [%elem{i}] it
    holds, and 0 when it holds none. *)
val type_arity : custom_case list -> int

(** The names the literal text of the type template [s] writes that C++
    does not declare itself -- every name but the builtin type words, a hole
    and a member of what a hole is filled with: what some header has to
    declare. *)
val declared_type_names : string -> string list

(** The standard-library names the literal text of [tokens] writes, each
    with the standard header declaring it ([("std::max", "algorithm")]),
    sorted.  A name the table behind this does not know is left out: it is
    a heuristic, which may miss a name but never invents a header. *)
val standard_names_written : custom_case list -> (string * string) list

(** How a match template binds its one branch's binders. *)
type binding = By_reference | By_value

(** The binding mode of a match template that is a structured binding of the
    scrutinee in front of the branch -- [const auto& [%b0a0, %b0a1] = %scrut;
    %br0] binds by reference, [auto [%b0a0, %b0a1] = %scrut; %br0] by value
    -- the one shape whose binding mode is not the mapping's to fix: whoever
    takes the scrutinee apart may bind it either way.  [None] for any other
    template. *)
val structured_binding : string -> binding option

(** [bound_by_value s] is the structured binding [s] binding by value. *)
val bound_by_value : string -> string

(** Whether the match template [s] declares branch [i]'s binder [j] as a
    variable of its own, by value: [auto %b1a1 = %scrut.tail();], its type
    [auto], a type argument or its own type hole, and no reference.  Such a
    binder holds a copy, not a part of the scrutinee, and is the branch's to
    move. *)
val declared_by_value : string -> int -> int -> bool

(** [Some (tests, final)] when the match template [s] is a chain of
    conditionals on its scrutinee, binding nothing:
    [if (T0) { %br{i0} } else if (T1) { %br{i1} } ... else { %br{k} }],
    each test [T] the tokens of its literal text and [%scrut], paired with
    the branch it runs; [final] the branch of the closing [else], if there
    is one. *)
val conditional_chain : string -> ((custom_case list * int) list * int option) option
