(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Names
open Miniml

type t = Digest.t

(** A serialization of one structure.  Every constructor writes a distinct
    tag and every list its length, so two different trees cannot write the
    same text. *)
type writer = {
  buf : Buffer.t;
  holes : (int, int) Hashtbl.t;
  metas : (int, int) Hashtbl.t;
}

let writer () =
  { buf = Buffer.create 4096; holes = Hashtbl.create 8; metas = Hashtbl.create 8 }

let tag w s = Buffer.add_string w.buf s; Buffer.add_char w.buf ' '

let str w s =
  Buffer.add_string w.buf (string_of_int (String.length s));
  Buffer.add_char w.buf ':';
  Buffer.add_string w.buf s;
  Buffer.add_char w.buf ' '

let int w i = tag w (string_of_int i)
let bool w b = tag w (if b then "t" else "f")

let list w f l = int w (List.length l); List.iter f l
let array w f a = int w (Array.length a); Array.iter f a
let option w f = function None -> tag w "-" | Some x -> tag w "+"; f x

(** [first_occurrence tbl k] numbers [k] by the order keys were first seen. *)
let first_occurrence tbl k =
  match Hashtbl.find_opt tbl k with
  | Some n -> n
  | None ->
    let n = Hashtbl.length tbl in
    Hashtbl.add tbl k n;
    n

let id w x = str w (Id.to_string x)
let label w l = str w (Label.to_string l)
let kername w kn = str w (KerName.to_string kn)
let mutind w m = kername w (MutInd.user m)
let modpath w mp = str w (ModPath.to_string mp)
let mbid w b = str w (MBId.to_string b)

let globref w = function
  | GlobRef.VarRef v -> tag w "V"; id w v
  | ConstRef c -> tag w "C"; kername w (Constant.user c)
  | IndRef (m, i) -> tag w "I"; mutind w m; int w i
  | ConstructRef ((m, i), j) -> tag w "K"; mutind w m; int w i; int w j

let kill_reason w = function
  | Ktype -> tag w "Ktype"
  | Kprop -> tag w "Kprop"
  | Kimplicit (r, n) -> tag w "Kimplicit"; globref w r; int w n

let sign w = function Keep -> tag w "Keep" | Kill k -> tag w "Kill"; kill_reason w k

let ml_ident w = function
  | Dummy -> tag w "Dummy"
  | Id x -> tag w "Id"; id w x
  | Tmp x -> tag w "Tmp"; id w x

let scheme_id w s = globref w (Scheme.Id.owner s); int w (Scheme.Id.arity s)

let rec ml_type w = function
  | Tarr (a, b) -> tag w "Tarr"; ml_type w a; ml_type w b
  | Tglob (r, tys, args) ->
    tag w "Tglob"; globref w r; list w (ml_type w) tys; list w (ml_ast w) args
  | Tvar (rigidity, i) ->
    tag w (match rigidity with Schematic -> "Tvar" | Rigid -> "Tvar!"); int w i
  | Tapp (i, tys) -> tag w "Tapp"; int w i; list w (ml_type w) tys
  | Tmeta {contents = Some t; _} -> ml_type w t
  | Tmeta {id = m; contents = None} -> tag w "Tmeta"; int w (first_occurrence w.metas m)
  | Thole h -> tag w "Thole"; int w (first_occurrence w.holes h)
  | Topen o -> tag w "Topen"; int w (first_occurrence w.metas (Open.id o))
  | Tdummy k -> tag w "Tdummy"; kill_reason w k
  | Tunknown -> tag w "Tunknown"
  | Taxiom -> tag w "Taxiom"
  | Tstring -> tag w "Tstring"

and ml_ast w = function
  | MLrel i -> tag w "MLrel"; int w i
  | MLapp (f, args) -> tag w "MLapp"; ml_ast w f; list w (ml_ast w) args
  | MLlam (x, ty, b) -> tag w "MLlam"; ml_ident w x; ml_type w ty; ml_ast w b
  | MLletin (x, ty, a, b) ->
    tag w "MLletin"; ml_ident w x; ml_type w ty; ml_ast w a; ml_ast w b
  | MLglob u -> tag w "MLglob"; global_use w u
  | MLcons (ty, r, args) ->
    tag w "MLcons"; ml_type w ty; globref w r; list w (ml_ast w) args
  | MLtuple args -> tag w "MLtuple"; list w (ml_ast w) args
  | MLcase (ty, a, brs) -> tag w "MLcase"; ml_type w ty; ml_ast w a; array w (branch w) brs
  | MLfix (i, ids, bodies, cofix, _) ->
    tag w "MLfix"; int w i;
    array w (fun (x, ty) -> id w x; ml_type w ty) ids;
    array w (ml_ast w) bodies;
    bool w cofix
  | MLexn s -> tag w "MLexn"; str w s
  | MLdummy k -> tag w "MLdummy"; kill_reason w k
  | MLaxiom s -> tag w "MLaxiom"; str w s
  | MLmagic (m, a) -> tag w "MLmagic"; magic w m; ml_ast w a
  | MLuint n -> tag w "MLuint"; str w (Uint63.to_string n)
  | MLfloat f -> tag w "MLfloat"; str w (Float64.to_hex_string f)
  | MLstring s -> tag w "MLstring"; str w (Pstring.to_string s)
  | MLparray (xs, d) -> tag w "MLparray"; array w (ml_ast w) xs; ml_ast w d

and magic w = function
  | Mcoerce (a, b) -> tag w "Mcoerce"; ml_type w a; ml_type w b
  | Mboxed -> tag w "Mboxed"
  | Mbarrier -> tag w "Mbarrier"

and branch w (binders, ty, pat, body) =
  list w (fun (x, t) -> ml_ident w x; ml_type w t) binders;
  ml_type w ty; pattern w pat; ml_ast w body

and pattern w = function
  | Pcons (r, ps) -> tag w "Pcons"; globref w r; list w (pattern w) ps
  | Ptuple ps -> tag w "Ptuple"; list w (pattern w) ps
  | Prel i -> tag w "Prel"; int w i
  | Pwild -> tag w "Pwild"
  | Pusual r -> tag w "Pusual"; globref w r

and global_use w u =
  globref w (Global_use.callee u);
  match Global_use.instantiation u with
  | None -> tag w "mono"
  | Some inst ->
    tag w "poly";
    scheme_id w (Scheme.Instantiation.scheme inst);
    Scheme.Instantiation.fold
      (fun v (s : ml_type Scheme.slot) () ->
        int w (Scheme.Var.ordinal v);
        ( match s.solution with
        | Identity -> tag w "identity"
        | Type t -> tag w "type"; ml_type w t );
        match s.source with
        | Not_written -> tag w "unwritten"
        | Written {binder; observed} ->
          tag w "written";
          int w (Scheme.Binder.position binder);
          option w (ml_type w) observed )
      inst ()

let record_field w (r, ty) = option w (globref w) r; ml_type w ty

let ind_kind w = function
  | Coinductive -> tag w "Coinductive"
  | Standard -> tag w "Standard"
  | Record fs -> tag w "Record"; list w (record_field w) fs
  | TypeClass fs -> tag w "TypeClass"; list w (record_field w) fs

let packet w p =
  id w p.ip_typename;
  array w (id w) p.ip_consnames;
  bool w p.ip_logical;
  list w (sign w) p.ip_sign;
  list w (id w) p.ip_vars;
  array w (list w (ml_type w)) p.ip_types;
  array w (list w (option w (id w))) p.ip_consarg_names

let ml_ind w ind =
  ind_kind w ind.ind_kind;
  int w ind.ind_nparams;
  array w (packet w) ind.ind_packets;
  match ind.ind_equiv with
  | NoEquiv -> tag w "NoEquiv"
  | Equiv kn -> tag w "Equiv"; kername w kn
  | RenEquiv s -> tag w "RenEquiv"; str w s

let fix_def w {fd_ref; fd_body; fd_type} =
  globref w fd_ref; ml_ast w fd_body; ml_type w fd_type

let ml_decl w = function
  | Dind (m, ind) -> tag w "Dind"; mutind w m; ml_ind w ind
  | Dtype (r, vars, ty) -> tag w "Dtype"; globref w r; list w (id w) vars; ml_type w ty
  | Dterm (r, a, ty) -> tag w "Dterm"; globref w r; ml_ast w a; ml_type w ty
  | Dfix fds -> tag w "Dfix"; list w (fix_def w) fds

let ml_spec w = function
  | Sind (m, ind) -> tag w "Sind"; mutind w m; ml_ind w ind
  | Stype (r, vars, ty) ->
    tag w "Stype"; globref w r; list w (id w) vars; option w (ml_type w) ty
  | Sval (r, a, ty) -> tag w "Sval"; globref w r; ml_ast w a; ml_type w ty

let rec module_type w = function
  | MTident mp -> tag w "MTident"; modpath w mp
  | MTfunsig (b, a, r) -> tag w "MTfunsig"; mbid w b; module_type w a; module_type w r
  | MTsig (mp, sg) -> tag w "MTsig"; modpath w mp; list w (module_sig_elem w) sg
  | MTwith (mt, wd) -> tag w "MTwith"; module_type w mt; with_decl w wd

and module_sig_elem w (l, sp) =
  label w l;
  match sp with
  | Spec s -> tag w "Spec"; ml_spec w s
  | Smodule mt -> tag w "Smodule"; module_type w mt
  | Smodtype mt -> tag w "Smodtype"; module_type w mt

and with_decl w = function
  | ML_With_type (path, vars, ty) ->
    tag w "With_type"; list w (id w) path; list w (id w) vars; ml_type w ty
  | ML_With_module (path, mp) -> tag w "With_module"; list w (id w) path; modpath w mp

let rec structure_elem w (l, se) =
  label w l;
  match se with
  | SEdecl d -> tag w "SEdecl"; ml_decl w d
  | SEmodule m -> tag w "SEmodule"; module_expr w m.ml_mod_expr; module_type w m.ml_mod_type
  | SEmodtype mt -> tag w "SEmodtype"; module_type w mt

and module_expr w = function
  | MEident mp -> tag w "MEident"; modpath w mp
  | MEfunctor (b, mt, me) -> tag w "MEfunctor"; mbid w b; module_type w mt; module_expr w me
  | MEstruct (mp, sel) -> tag w "MEstruct"; modpath w mp; list w (structure_elem w) sel
  | MEapply (f, x) -> tag w "MEapply"; module_expr w f; module_expr w x

let digest write x =
  let w = writer () in
  write w x;
  Digest.string (Buffer.contents w.buf)

let structure =
  digest (fun w s -> list w (fun (mp, sel) -> modpath w mp; list w (structure_elem w) sel) s)

let elements s =
  List.concat_map
    (fun (_, sel) -> List.map (fun ((l, _) as e) -> (l, digest structure_elem e)) sel)
    s

let decl = digest ml_decl
let equal = Digest.equal
let to_hex = Digest.to_hex
