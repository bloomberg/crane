(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* How a machine's frames hold its loops' parameters: by pointer where
   every value passed for one lies in what the caller passed, the greatest
   such set, through the loops its entries enter. *)

open Crane_plugin
open Names
open Miniml
open Control_ir
module Storage = Ownership_plan.Storage

let check name cond =
  if not cond then (
    Printf.eprintf "frame_storage: %s\n" name;
    exit 1 )

let r s = GlobRef.VarRef (Id.of_string s)
let id s = Id (Id.of_string s)
let nat = Tglob (r "nat", [], [])
let tree = Tglob (r "tree", [], [])
let lst = Tglob (r "lst", [], [])
let node = r "node"
let cons = r "cons"
let nil = r "nil"
let f = Loop.Function (r "f")
let sizes = Loop.Member (Occurrence.fresh (), 0)

(* [node] keeps its two subtrees and [cons] its tail behind the pointer;
   [cons]'s head is held in the cell. *)
let pointer_fields c =
  if GlobRef.UserOrd.equal c node then Some [0; 1] else if GlobRef.UserOrd.equal c cons then Some [1] else None

let plan ?(holdable = fun _ -> true) l = Frame_storage.plan ~pointer_fields ~in_place:(fun _ _ -> false) ~holdable l
let app g args = MLapp (MLglob (Global_use.monomorphic (r g)), args)
let continue_ target arguments = Term.Continue {target; occurrence = Occurrence.fresh (); arguments}

(* let x := <continue> in <body>, as a machine resumes after a call. *)
let resume value body = Term.Resume {binder = id "x"; binder_type = nat; value; body}

let branch ?(binders = []) pattern body : Term.branch = {binders; result_type = nat; pattern; body}
let match_ ty scrutinee branches = Term.Match {scrutinee_type = ty; scrutinee; branches}

(* match t with node l r => size l + size r, under [t]. *)
let size_body pass_left =
  match_ tree (fresh_rel 1)
    [ branch
        ~binders:[(id "l", tree); (id "r", tree)]
        (Pcons (node, [Prel 2; Prel 1]))
        (resume (continue_ f [pass_left]) (resume (continue_ f [fresh_rel 2]) (Term.Return (app "plus" [fresh_rel 1; fresh_rel 2])))) ]

let () =
  let size pass = {Term.loop = f; parameters = [(id "t", tree)]; body = size_body pass} in
  check "a subtree behind the pointer is held by pointer" ((plan (size (fresh_rel 2))).own = [Storage.Local]);
  check "a value a call made is held by value" ((plan (size (app "mirror" [fresh_rel 2]))).own = [Storage.Frame]);

  (* tree_size t := match t with node n kids => n + sizes kids, sizes the
     entered fixpoint over a list of trees: sizes (cons a rest) :=
     tree_size a + sizes rest.  [kids] is the second subtree here. *)
  let entered pass_rest =
    { Term.loop = sizes;
      parameters = [(id "ts", lst)];
      body =
        match_ lst (fresh_rel 1)
          [ branch (Pusual nil) (Term.Return (MLdummy Kprop));
            branch
              ~binders:[(id "a", tree); (id "rest", lst)]
              (Pcons (cons, [Prel 2; Prel 1]))
              (resume (continue_ f [fresh_rel 2]) (resume (continue_ sizes [pass_rest]) (Term.Return (fresh_rel 1)))) ] }
  in
  let machine ?(pass_rest = fresh_rel 2) pass_kids =
    { Term.loop = f;
      parameters = [(id "t", tree)];
      body =
        match_ tree (fresh_rel 1)
          [ branch
              ~binders:[(id "n", tree); (id "kids", tree)]
              (Pcons (node, [Prel 2; Prel 1]))
              (Term.Entry {entered = entered pass_rest; name = None; scope = continue_ sizes [pass_kids]}) ] }
  in
  let p = plan (machine (fresh_rel 1)) in
  check "the machine's parameter, passed a cell's head, is held by pointer" (p.own = [Storage.Local]);
  (* The entered body stands under [t], [n], [kids] and the fixpoint's name. *)
  check "the entered parameter is held by pointer, at its level" (p.entered = [(4, Storage.Local)]);
  let p = plan (machine (app "rebuild" [fresh_rel 1])) in
  check "an entered parameter passed a value a call made is held by value" (p.entered = [(4, Storage.Frame)]);
  check "and what is passed on of it is no pointer either" (p.own = [Storage.Frame]);
  (* A turn passing the tail through a let copies the list it reads. *)
  let p =
    plan
      { (machine (fresh_rel 1)) with
        body =
          match_ tree (fresh_rel 1)
            [ branch
                ~binders:[(id "n", tree); (id "kids", tree)]
                (Pcons (node, [Prel 2; Prel 1]))
                (Term.Let {binder = id "k"; binder_type = lst; value = fresh_rel 1; body = Term.Entry {entered = entered (fresh_rel 2); name = None; scope = continue_ sizes [fresh_rel 1]}}) ] }
  in
  check "a let's copy is held by value" (p.entered = [(5, Storage.Frame)]);
  (* A parameter its lowering holds by value is a copy in its frame: what
     is passed on of it is no pointer either. *)
  let p = plan ~holdable:(function Frame_storage.Own _ -> false | Entered _ -> true) (machine (fresh_rel 1)) in
  check "a parameter held by value is no pointer" (p.own = [Storage.Frame]);
  check "nor what an entered loop is passed of it" (p.entered = [(4, Storage.Frame)]);
  (* An entered parameter is asked about by its loop and position. *)
  let asked = ref [] in
  let p =
    plan
      ~holdable:(function
        | Frame_storage.Own _ -> true
        | Entered {loop; index; level} ->
          asked := (loop.loop, index, level) :: !asked;
          false )
      (machine (fresh_rel 1))
  in
  check "the entered parameter is asked about by its loop, position and level"
    (match !asked with [(l, 0, 4)] -> Loop.equal l sizes | _ -> false);
  check "and held by value where it is not holdable, with what it passes on" (p.entered = [(4, Storage.Frame)] && p.own = [Storage.Frame]);

  (* A local fixpoint's plan: what translation recorded of each function. *)
  let o = Occurrence.fresh () in
  let member = Loop.Member (o, 0) in
  let loop parameters = {Term.loop = member; parameters; body = Term.Return (fresh_rel 1)} in
  check "a function's loop has no local plan" (Frame_storage.local_holdable (machine (fresh_rel 1)) 0 = None);
  check "nor a member translation generated no lambda for" (Frame_storage.local_holdable (loop [(id "t", tree)]) 0 = None);
  Ownership_plan.Local_passing.record (o, 0) [None; Some Callable_abi.Borrowed; Some Callable_abi.Forwarded];
  check "the plan is looked up by the member"
    (Ownership_plan.Local_passing.lookup (o, 0) = Some [None; Some Callable_abi.Borrowed; Some Callable_abi.Forwarded]);
  check "of another function of the group nothing is recorded" (Ownership_plan.Local_passing.lookup (o, 1) = None);
  let l = loop [(id "p", nat); (id "t", tree); (id "k", nat)] in
  check "a parameter of no runtime value is held by no pointer" (Frame_storage.local_holdable l 0 = Some false);
  check "a lent parameter of a type the program knows no inductive of is held by value"
    (Frame_storage.local_holdable l 1 = Some false);
  check "a forwarded parameter is held by value" (Frame_storage.local_holdable l 2 = Some false);
  check "no value is held by pointer that is not lent" (not (Frame_storage.passed_holdable None tree))
