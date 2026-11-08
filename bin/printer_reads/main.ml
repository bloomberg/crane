(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** [printer_reads DIR ROOT TARGET]: every value of module [TARGET] that a
    value of module [ROOT] reaches, through any chain of the plugin's
    top-level values, with one shortest chain each.

    [printer_reads DIR ROOT TARGET VALUE]: every edge by which a value of
    [ROOT] leaves [ROOT] for a value that reaches [TARGET.VALUE] -- all the
    ways in, where the first form shows one.

    The graph is read off the typed trees dune writes ([DIR/*.cmt]): a node is
    a module's top-level value, an edge a reference to one in its body.  It is
    insensitive to control flow -- a reference in a branch never taken still
    counts -- except that the branch [if Probe.checking () then ..] is
    skipped: an oracle run under CRANE_CHECK_IR may read what it likes.  A
    module with no typed tree in [DIR] (Rocq's, the standard library) is a
    leaf.  Used by scripts/check-module-deps.sh for the printer's indirect
    reads of Table. *)

let library_prefix = "Crane_plugin__"

let strip s =
  let n = String.length library_prefix in
  if String.length s >= n && String.sub s 0 n = library_prefix then String.sub s n (String.length s - n) else s

type node = string * string (* module, value (dotted inside a submodule) *)

let edges : (node, node list) Hashtbl.t = Hashtbl.create 4096
let defined : (string, node list) Hashtbl.t = Hashtbl.create 256

let analyse cmt_file =
  let cmt = Cmt_format.read_cmt cmt_file in
  let m = strip cmt.Cmt_format.cmt_modname in
  match cmt.Cmt_format.cmt_annots with
  | Cmt_format.Implementation str ->
    let values : (Ident.t, string) Hashtbl.t = Hashtbl.create 256 in
    let modules : (Ident.t, string * string) Hashtbl.t = Hashtbl.create 16 in
    let rec resolve_module (p : Path.t) =
      match p with
      | Pident id -> (
        match Hashtbl.find_opt modules id with Some r -> Some r | None -> Some (strip (Ident.name id), "") )
      | Pdot (Pident id, name) when Ident.name id = "Crane_plugin" -> Some (name, "")
      | Pdot (q, name) -> Option.map (fun (mm, pre) -> (mm, pre ^ name ^ ".")) (resolve_module q)
      | _ -> None
    in
    let resolve_value (p : Path.t) =
      match p with
      | Pident id -> Option.map (fun n -> (m, n)) (Hashtbl.find_opt values id)
      | Pdot (q, v) -> Option.map (fun (mm, pre) -> (mm, pre ^ v)) (resolve_module q)
      | _ -> None
    in
    let rec unwrap (me : Typedtree.module_expr) =
      match me.mod_desc with Tmod_constraint (me, _, _, _) -> unwrap me | d -> d
    in
    (* First the names, so that a reference to a later value resolves. *)
    let rec register pre (str : Typedtree.structure) =
      List.iter
        (fun (item : Typedtree.structure_item) ->
          match item.str_desc with
          | Tstr_value (_, vbs) ->
            List.iter
              (fun (vb : Typedtree.value_binding) ->
                List.iter
                  (fun id -> Hashtbl.replace values id (pre ^ Ident.name id))
                  (Typedtree.pat_bound_idents vb.vb_pat) )
              vbs
          | Tstr_module {mb_id = Some id; mb_expr; _} -> (
            match unwrap mb_expr with
            | Tmod_structure s ->
              let pre' = pre ^ Ident.name id ^ "." in
              Hashtbl.replace modules id (m, pre');
              register pre' s
            | Tmod_ident (p, _) -> Option.iter (Hashtbl.replace modules id) (resolve_module p)
            | _ -> () )
          | _ -> () )
        str.str_items
    in
    register "" str;
    let is_checking (e : Typedtree.expression) =
      let found = ref false in
      let it =
        { Tast_iterator.default_iterator with
          expr =
            (fun self e ->
              ( match e.exp_desc with
              | Texp_ident (p, _, _) when resolve_value p = Some ("Probe", "checking") -> found := true
              | _ -> () );
              Tast_iterator.default_iterator.expr self e ) }
      in
      it.expr it e;
      !found
    in
    let refs_of (vb : Typedtree.value_binding) =
      let acc = ref [] in
      let it =
        { Tast_iterator.default_iterator with
          expr =
            (fun self e ->
              match e.exp_desc with
              | Texp_ident (p, _, _) ->
                Option.iter (fun n -> acc := n :: !acc) (resolve_value p)
              | Texp_ifthenelse (c, _, otherwise) when is_checking c ->
                self.expr self c;
                Option.iter (self.expr self) otherwise
              | _ -> Tast_iterator.default_iterator.expr self e ) }
      in
      it.value_binding it vb;
      !acc
    in
    let rec walk (str : Typedtree.structure) =
      List.iter
        (fun (item : Typedtree.structure_item) ->
          match item.str_desc with
          | Tstr_value (_, vbs) ->
            List.iter
              (fun (vb : Typedtree.value_binding) ->
                let rs = refs_of vb in
                List.iter
                  (fun id ->
                    let n = (m, Hashtbl.find values id) in
                    Hashtbl.replace defined m (n :: Option.value ~default:[] (Hashtbl.find_opt defined m));
                    Hashtbl.replace edges n rs )
                  (Typedtree.pat_bound_idents vb.vb_pat) )
              vbs
          | Tstr_module {mb_expr; _} -> ( match unwrap mb_expr with Tmod_structure s -> walk s | _ -> ())
          | _ -> () )
        str.str_items
    in
    walk str
  | _ -> ()

let load dir root =
  Array.iter (fun f -> if Filename.check_suffix f ".cmt" then analyse (Filename.concat dir f)) (Sys.readdir dir);
  match Hashtbl.find_opt defined root with
  | None ->
    prerr_endline ("printer_reads: no typed tree for " ^ root ^ " in " ^ dir);
    exit 2
  | Some _ -> ()

(* The edges from a value of [root] to a value outside it that reaches
   [goal], one line each. *)
let frontier root goal =
  let memo : (node, bool) Hashtbl.t = Hashtbl.create 4096 in
  let rec reaches n =
    match Hashtbl.find_opt memo n with
    | Some b -> b
    | None ->
      Hashtbl.replace memo n false;
      let b = n = goal || List.exists reaches (Option.value ~default:[] (Hashtbl.find_opt edges n)) in
      Hashtbl.replace memo n b;
      b
  in
  let found = ref [] in
  List.iter
    (fun n ->
      List.iter
        (fun s -> if fst s <> root && reaches s then found := (snd n ^ "\t" ^ fst s ^ "." ^ snd s) :: !found)
        (Option.value ~default:[] (Hashtbl.find_opt edges n)) )
    (Hashtbl.find defined root);
  List.iter print_endline (List.sort_uniq compare !found)

let () =
  match Sys.argv with
  | [|_; dir; root; target; value|] ->
    load dir root;
    frontier root (target, value)
  | [|_; dir; root; target|] ->
    load dir root;
    (* Breadth first, so each value is reported with a shortest chain. *)
    let parent : (node, node option) Hashtbl.t = Hashtbl.create 4096 in
    let queue = Queue.create () in
    List.iter
      (fun n -> if not (Hashtbl.mem parent n) then (Hashtbl.replace parent n None; Queue.add n queue))
      (List.sort compare (Hashtbl.find defined root));
    let found = ref [] in
    while not (Queue.is_empty queue) do
      let n = Queue.pop queue in
      if fst n = target then found := n :: !found
      else
        List.iter
          (fun s ->
            if not (Hashtbl.mem parent s) then begin
              Hashtbl.replace parent s (Some n);
              Queue.add s queue
            end )
          (List.sort_uniq compare (Option.value ~default:[] (Hashtbl.find_opt edges n)))
    done;
    let rec chain n =
      let s = fst n ^ "." ^ snd n in
      match Hashtbl.find parent n with None -> [s] | Some p -> chain p @ [s]
    in
    List.iter
      (fun n -> print_endline (snd n ^ "\t" ^ String.concat " > " (chain n)))
      (List.sort compare !found)
  | _ ->
    prerr_endline "usage: printer_reads DIR ROOT TARGET [VALUE]";
    exit 2
