(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The Perceus reuse cursor of a loop built tail modulo cons, decided over
    its ControlIR: each turn's outermost allocation reuses the storage of the
    input cell the loop frees in that turn.  Read when the loop is lowered
    to MiniCpp ([Control_to_cpp_ir]) and checked by [Loopify_tmc].

    A loop built tail modulo cons walks an input of the type it builds, a
    turn at a time, and builds one cell of its output per turn.  Where the
    loop owns the input, the cell it stands on is dead once the turn has
    read it, and can be rebuilt in place as the turn's outermost cell
    instead of being freed while a fresh one is allocated.  The loop then
    holds the cell it stands on by an owning handle, which each turn that
    rebuilds a cell trades for an owning handle on the field it walks on to,
    stolen from the cell before the cell is rebuilt.

    Three things make that sound, and each is a fact of the loop's ControlIR:
    the cell the loop stands on is always the one the handle owns, so every
    turn passes the walked parameter either itself or a field stored behind
    the pointer of the cell a match on it takes apart, never anything else,
    and every turn walking on steps the handle -- one building nothing
    releases the cell it leaves instead of rebuilding it; the rebuilt cell is
    of the walked parameter's type, its storage the right size; and nothing
    the turn reads of the cell is read after the field was stolen or the cell
    rebuilt or released.

    Whether the loop owns its input, and whether its result is assembled in
    heap cells the cursor can recycle into, are its lowering's: they are how
    the function's head passes the parameter and how the result type is
    represented. *)

(** What a turn walking the cursor on does with the cell it leaves.
    [Recycle] rebuilds it as the turn's outermost cell, a [Continue_into],
    and [cells_read_first] are the arguments of the turn's cells it must read
    before the steal, each [(cell, argument)] the position of a cell among
    the turn's, outermost first, and of an argument among its constructor's
    declared ones: the outermost cell's arguments are evaluated before it is
    rebuilt, but after the steal, so only those reading the stolen field, or
    the whole cell, are; of the inner cells, every one reading anything the
    cell holds.  [Release] frees it, a [Continue] building nothing. *)
type action =
  | Recycle of {cells_read_first : (int * int) list}
  | Release

(** A turn that walks the cursor on: the turn [turn], the recursive call
    heading it, what it does with the cell it leaves, and
    [arguments_read_first], positions among the loop's parameters of the
    arguments the turn passes them that read anything the cell holds, and
    are read before the field it walks on to is stolen. *)
type step = private {
  turn : Miniml.Occurrence.t;
  action : action;
  arguments_read_first : int list;
}

(** The loop's cursor: the position [parameter] among the loop's parameters
    of the input it walks, and every turn that walks it on, at least one
    recycling. *)
type t = private {
  parameter : int;
  steps : step list;
}

(** [plan ~pointer_fields ~in_place l]: the cursor of the loop [l], built
    tail modulo cons, if it has one.  It is the one parameter every turn of
    [l] passes either itself or a field stored behind the pointer, as
    [pointer_fields] says of a constructor's declared arguments, by a match
    on the parameter itself, every turn that does and builds cells building
    the outermost one of the parameter's type, and at least one so building.
    An in-place coercion ([in_place from into]) changes nothing a parameter
    stands for.  [None] where no parameter, or more than one, is so
    walked. *)
val plan :
  pointer_fields:(Names.GlobRef.t -> int list option) ->
  in_place:(Miniml.ml_type -> Miniml.ml_type -> bool) ->
  Control_ir.Term.loop ->
  t option

(** [positioned c positions]: [c] for what lowers its loop, taking
    parameters each standing, in order, for the parameter of the loop at
    [positions], or for none of them; [None] where the cursor's own
    parameter is not among them. *)
val positioned : t -> int option list -> t option

(** The step [c] takes at the turn [turn], if it walks on there. *)
val step_at : t -> Miniml.Occurrence.t -> step option
