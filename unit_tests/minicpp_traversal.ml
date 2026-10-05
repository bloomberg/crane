(* Every type a MiniCpp declaration carries is reached by [Minicpp.map_decl].

   A sentinel type is planted at each place a type can sit -- template-
   parameter defaults, callable constraints and concept arguments at every
   level that has a template head, an inline mapping's recorded result type,
   nested aliases, member signatures -- and the traversal must visit every
   one.  A place it skips is a place the settled checker and the erasure
   passes cannot see. *)

open Names
open Crane_plugin
open Minicpp

let sentinel = Tid (Id.of_string "Sentinel", [])
let r name = GlobRef.VarRef (Id.of_string name)
let id = Id.of_string

(* Planting a sentinel counts it, so the expected total is never written by
   hand. *)
let planted = ref 0

let s () =
  incr planted;
  sentinel

let tparams () =
  [ (TTtypename_default (s ()), id "A");
    (TTfun ([s ()], s ()), id "F");
    (TTconcept (r "C", [s ()]), id "I") ]

let method_ () =
  { mf_name = id "m";
    mf_globref = None;
    mf_tparams = tparams ();
    mf_ret_type = s ();
    mf_params = [(id "p", s ())];
    mf_body =
      [ Sreturn
          (Some
             (CPPglob
                ( r "g",
                  [s ()],
                  Some
                    { ci_inline = None;
                      ci_yields = Some (s ()) } ))) ];
    mf_receiver = Static;
    mf_is_inline = false;
    mf_no_pure = false;
    mf_is_noexcept = false;
    mf_kind = Ordinary }

let struct_ () =
  { ds_ref = r "S";
    ds_fields =
      [ (Fmethod (method_ ()), VPublic, SNoTag);
        ( Fconstructor
            { fc_tparams = tparams ();
              fc_params = [(id "x", s ())];
              fc_inits = [];
              fc_body = [];
              fc_explicit = false;
              fc_noexcept = false },
          VPublic,
          SNoTag );
        (Fnested_using (tparams (), id "U", s ()), VPublic, SNoTag);
        ( Fnested_struct (id "N", [(Fvar (id "v", s ()), VPublic, SNoTag)]),
          VPublic,
          SNoTag );
        (Fmember_decl (OLmethod (method_ ())), VPublic, SNoTag) ];
    ds_tparams = tparams ();
    ds_constraint = None;
    ds_needs_shared_from_this = false }

let decl () =
  Dnspace
    ( None,
      [ Dtemplate (tparams (), None, Dstruct (struct_ ()));
        Dfields (struct_ ());
        Dstruct_fwd (tparams (), r "S");
        Dusing
          { du_tparams = tparams ();
            du_name = r "U";
            du_rhs = Some (s ());
            du_note = None };
        Dmember_def
          { dm_owner = r "S";
            dm_enclosing = None;
            dm_tparams = tparams ();
            dm_field = OLmethod (method_ ()) };
        Denum
          { de_ref = r "E";
            de_ctors = [];
            de_ctor_rocq_names = [];
            de_tparams = tparams () } ] )

let () =
  let d = decl () in
  let seen = ref 0 in
  let ft =
    map_cpp_type (fun t ->
        if t = sentinel then incr seen;
        t )
  in
  let rec fe e = map_expr fe fs ft e
  and fs st = map_stmt fe fs ft st in
  ignore (map_decl fe fs ft d);
  if !seen <> !planted then (
    Printf.eprintf "map_decl reached %d of %d planted types\n" !seen !planted;
    exit 1 )
