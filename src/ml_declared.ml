(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** MiniML read through declared meanings.  See [ml_declared.mli]. *)

open Miniml

let rec pure = function
  | MLrel _ | MLuint _ | MLfloat _ | MLstring _ -> true
  | MLcons (_, _, args) | MLtuple args -> List.for_all pure args
  | MLapp (MLglob (g, _), args) -> (
    match Mapping_semantics.find g with
    | Some (Mapping_semantics.Unsigned _) -> List.for_all pure args
    | _ -> false )
  | MLmagic (_, a) -> pure a
  | MLletin (_, _, a, b) -> pure a && pure b
  | MLcase (_, s, brs) -> pure s && Array.for_all (fun (_, _, _, b) -> pure b) brs
  | _ -> false

let definitions struc =
  let defs = ref Table.Refmap'.empty in
  let rec sel l =
    List.iter
      (fun (_, se) ->
        match se with
        | SEdecl (Dterm (r, body, _)) -> defs := Table.Refmap'.add r body !defs
        | SEdecl (Dfix fds) ->
          List.iter (fun fd -> defs := Table.Refmap'.add fd.fd_ref fd.fd_body !defs) fds
        | SEmodule {ml_mod_expr = MEstruct (_, l); _} -> sel l
        | _ -> ())
      l
  in
  List.iter (fun (_, l) -> sel l) struc;
  !defs

let map_decls f struc =
  let rec elems sel =
    List.map
      (fun (l, se) ->
        match se with
        | SEdecl d -> (l, SEdecl (f d))
        | SEmodule m -> (l, SEmodule {m with ml_mod_expr = module_expr m.ml_mod_expr})
        | se -> (l, se) )
      sel
  and module_expr = function
    | MEstruct (mp, sel) -> MEstruct (mp, elems sel)
    | MEfunctor (mbid, mt, me) -> MEfunctor (mbid, mt, module_expr me)
    | me -> me
  in
  List.map (fun (mp, sel) -> (mp, elems sel)) struc
