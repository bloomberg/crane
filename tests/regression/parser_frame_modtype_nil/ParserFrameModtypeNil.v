From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Crane Require Import Mapping.NatInt.
From Crane Require Import Mapping.DequeList.
From Stdlib Require Import List.
Import ListNotations.

(** Reproduces (now fixed) a compile-time failure in the extracted C++ parser
    core that appeared after the grammar_pairlist_nil_cons_mismatch fix landed:

      Parser.h: no viable conversion from
        'pair<Parser_frame, deque<any>>' to
        'pair<Parser_frame, deque<Parser_frame>>'

    The real code (theories/Parser) is layered across TWO functors joined by an
    ABSTRACT MODULE TYPE:

      * [theories/Parser/Defs.v] defines [parser_frame]/[parser_stack] inside
        [Module DefsFn (Export Ty : SymbolTypes)], then re-exposes DefsFn's
        contents through a *module type*:
            Module Type DefsT (SymTy : SymbolTypes). Include DefsFn SymTy. End DefsT.
            Module Type T. Declare Module SymTy : SymbolTypes.
                           Declare Module Defs : DefsT SymTy. ... End T.

      * [theories/Parser/Parser.v] defines the nil use-site inside a DIFFERENT
        functor over that module type:
            Module ParserFn (Import D : Defs.T).
              Definition parse ... := let sk0 := (Fr [] tt [NT x], []) in ...

    So at the literal outer [[]] (a [list parser_frame] nil), [parser_frame] is
    seen *abstractly*, through the module type [Defs.T] -- NOT through the
    concrete [DefsFn] output. That abstraction boundary is the essential
    trigger: standalone / same-functor variants of this exact frame/stack shape
    do NOT reproduce it (Crane emits [std::deque<Frame>{}] correctly). Only when
    the nil use is behind the [Include DefsFn]-inside-a-[Module Type] boundary
    does Crane's erasure collapse [list frame]'s nil to the fully-erased shape
    [std::deque<std::any>{}], while [frame]'s cons sites (in [push_frame] /
    [tail_lengths], reached from the concrete side) build/expect the concrete
    [std::deque<frame>] shape -- a compile-time "no viable conversion" error.

    Fix: the grammar_pairlist_nil_cons_mismatch [hollow_container] collapse (in
    [gen_expr_custom_cons]) fired whenever the list's ML element annotation was
    all-[Tdummy], forcing the element to bare [std::any].  It now additionally
    requires the concrete C++ element type ([temps]) to be erased too.  Here the
    abstract [frame] resolves to a fully-concrete [typename D::Defs::frame]
    despite the hollow ML annotation, so the concrete [std::deque<frame>] shape
    is preserved, while genuinely-erased lists (like the pairlist case) still
    collapse to [std::deque<std::any>]. *)

(* Mirrors [tuple] underlying Defs.v's [symbols_semty]. *)
Fixpoint tuple (xs : list Type) : Type :=
  match xs with
  | [] => unit
  | x :: xs' => prod x (tuple xs')
  end.

(* Mirrors [Module Type SymbolTypes] with its abstract [t_semty]/[nt_semty]. *)
Module Type SymbolTypes.
  Parameter symbol : Type.
  Parameter symbol_semty : symbol -> Type.
End SymbolTypes.

(* Mirrors [Module DefsFn (Export Ty : SymbolTypes)] defining [parser_frame],
   [parser_stack], and their manipulators over the ABSTRACT symbol family. *)
Module DefsFn (Export Ty : SymbolTypes).
  Definition symbols_semty (pre : list symbol) : Type :=
    tuple (List.map symbol_semty pre).

  (* Mirrors [parser_frame]. *)
  Inductive frame : Type :=
  | Fr (pre : list symbol) (sem : symbols_semty pre) (suf : list symbol).

  (* Mirrors [parser_stack]. *)
  Definition stack : Type := (frame * list frame)%type.

  (* Mirrors [step]/[multistep] pushing a new (non-nil) frame list -- the CONS
     counterpart that builds the concrete [std::deque<frame>] shape. *)
  Definition push_frame (f : frame) (s : stack) : stack :=
    match s with
    | (top, rest) => (f, top :: rest)
    end.

  (* Mirrors [unproc_tail_syms]: a Fixpoint destructuring [list frame] and the
     [Fr] constructor's own dependent fields -- another concrete-shape site. *)
  Fixpoint tail_lengths (frs : list frame) : nat :=
    match frs with
    | [] => 0
    | Fr _ _ suf :: frs' => List.length suf + tail_lengths frs'
    end.
End DefsFn.

(* Mirrors [Module Type DefsT (SymTy : SymbolTypes). Include DefsFn SymTy. End]. *)
Module Type DefsT (Ty : SymbolTypes).
  Include DefsFn Ty.
End DefsT.

(* Mirrors [Module Type T] bundling an abstract [SymTy] and [Defs : DefsT SymTy]. *)
Module Type T.
  Declare Module SymTy : SymbolTypes.
  Declare Module Defs  : DefsT SymTy.
  Export SymTy.
  Export Defs.
End T.

(* Mirrors [Module ParserFn (Import D : Defs.T)] in Parser.v: the outer [[]]
   ([list frame] nil) is used HERE, where [frame] is abstract (via [T]). *)
Module ParserFn (Import D : T).
  (* Mirrors [multistep]: consumes a stack (destructures head frame + tail). *)
  Definition step_stack (s : stack) : nat :=
    match s with
    | (Fr _ _ suf, frs) => List.length suf + tail_lengths frs
    end.

  (* Mirrors [parse]: [sk0] is a LET-bound intermediate passed to the consumer.
     At the C++ level it becomes [auto sk0 = std::make_pair(...)], so the nil
     [[]] gets erased with NO expected type flowing in from a return/param
     annotation -- exactly the configuration that misfires in the real Parser.h
     ([auto sk0 = ...; multistep(..., std::move(sk0), ...)]). A directly
     type-annotated [return (Fr [] tt [x], [])] does NOT reproduce it. *)
  Definition parse (x : symbol) : nat :=
    let sk0 := (Fr [] tt [x], []) in
    step_stack sk0.
End ParserFn.

(* Concrete instantiation -- mirrors JSON's [Module JSON_Symbol_Types <:
   SymbolTypes], [Module D <: Defs.T ... Module Defs := DefsFn SymTy], [Make D]. *)
Inductive concrete_symbol := SA | SB.
Definition concrete_symbol_semty (s : concrete_symbol) : Type :=
  match s with SA => nat | SB => bool end.

Module ConcreteSymTypes <: SymbolTypes.
  Definition symbol := concrete_symbol.
  Definition symbol_semty := concrete_symbol_semty.
End ConcreteSymTypes.

Module D <: T.
  Module        SymTy := ConcreteSymTypes.
  Module Export Defs  := DefsFn SymTy.
End D.

Module Export TheParser := ParserFn D.

Crane Extraction "parser_frame_modtype_nil"
  TheParser.parse TheParser.step_stack D.Defs.push_frame D.Defs.tail_lengths.
